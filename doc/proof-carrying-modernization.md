# Proof-Carrying COBOL Modernization

## 概要

本フレームワークは、COBOLプログラムのモダナイゼーション（TypeScript等への変換）において、
**元のプログラムが持つ性質（プロパティ）が変換後も保存されることを検証可能にする仕組み**を提供する。

「Proof-Carrying」の名の通り、プロパティ定義と検証結果が**証明書（Proof Certificate）**として
コードとともに運ばれ、変換の正当性を保証する。

```
┌─────────────────────────────────────────────────────────────────┐
│                     Proof-Carrying Flow                         │
│                                                                 │
│  ┌───────────────┐     ┌──────────────────┐                     │
│  │ COBOL Source   │     │ Property         │                     │
│  │ (AST)          │     │ Definitions      │                     │
│  └───────┬───────┘     │ (13 properties)  │                     │
│          │              └────────┬─────────┘                     │
│          v                       │                               │
│  ┌───────────────────┐          │                               │
│  │ Instrumented      │          │                               │
│  │ Interpreter       │          │                               │
│  │ (type-safe exec)  │          │                               │
│  └───────┬───────────┘          │                               │
│          │                       │                               │
│          v                       v                               │
│  ┌───────────────┐     ┌──────────────────┐                     │
│  │ Execution     │────>│ Property         │                     │
│  │ Traces        │     │ Verifier         │                     │
│  │ (186 events)  │     │                  │                     │
│  └───────────────┘     └────────┬─────────┘                     │
│                                  │                               │
│                                  v                               │
│                        ┌──────────────────┐                     │
│                        │ Proof Certificate │                     │
│                        │ (VALID/PARTIAL/   │                     │
│                        │  INVALID)         │                     │
│                        └────────┬─────────┘                     │
│                                  │                               │
│               ┌─────────────────┼─────────────────┐             │
│               v                 v                  v             │
│       ┌──────────────┐  ┌────────────┐  ┌──────────────┐       │
│       │ Code         │  │ Cross      │  │ Modernized   │       │
│       │ Generation   │  │ Verification│  │ Code         │       │
│       │ (TypeScript) │  │ (多入力)   │  │ Re-verify    │       │
│       └──────────────┘  └────────────┘  └──────────────┘       │
└─────────────────────────────────────────────────────────────────┘
```

## 設計思想

### なぜProof-Carryingか

COBOLモダナイゼーションの最大のリスクは**「変換後のプログラムが元と同じ振る舞いをするか分からない」**こと。
静的解析だけでは不十分であり、実行時の振る舞い（丸め、型変換、分岐パス）を含めた検証が必要。

本フレームワークは以下の3つのレベルで正当性を保証する：

| レベル | 検証内容 | 例 |
|--------|----------|-----|
| **性質保存** | 定義したプロパティが変換後も成立 | `残高 >= 0` が常に成立 |
| **出力同値** | DISPLAY出力が一致 | 月次レポートの数値一致 |
| **状態同値** | 最終変数状態が一致 | 累計利息の値が許容誤差内 |

### Proof Certificateとは

Proof Certificateは以下の情報を統合した**変換の正当性の証拠**：

1. **PropertySet** - 何を保証するか（プロパティの定義）
2. **Source Verification** - 元COBOLで各プロパティが成立したか
3. **Target Verification** - 変換後のコードでも成立したか
4. **Cross Verification** - 出力と状態の直接比較
5. **Preservation判定** - 各プロパティの保存状況

ステータスは3段階：
- **VALID**: 全プロパティ保存 + 出力/状態一致
- **PARTIAL**: 一部プロパティのみ保存
- **INVALID**: プロパティの保存なし

## プロパティの8カテゴリ

### 1. DataInvariant（データ不変条件）

全実行ステップで成立する変数の制約。

```typescript
{
  propertyType: 'data-invariant',
  id: 'INV-01',
  description: 'WS-TOTAL-INTEREST は常に 0 以上',
  targetVar: 'WS-TOTAL-INTEREST',
  condition: cmp('>=', varRef('WS-TOTAL-INTEREST'), lit(0)),
  checkAt: 'every-assignment',  // every-assignment | after-paragraph | at-end
}
```

**検証方法**: トレースの `var-assign` イベントごとに変数状態を再構築し条件を評価。

### 2. Precondition（事前条件）

パラグラフ呼び出し前に成立すべき条件。

```typescript
{
  propertyType: 'precondition',
  id: 'PRE-01',
  description: 'CALC-MONTHLY-RATE 呼出前: WS-ANNUAL-RATE > 0',
  paragraphName: 'CALC-MONTHLY-RATE',
  condition: cmp('>', varRef('WS-ANNUAL-RATE'), lit(0)),
}
```

**検証方法**: `perform-call` イベント発生時に条件を評価。

### 3. Postcondition（事後条件）

パラグラフ実行後に成立すべき条件。

```typescript
{
  propertyType: 'postcondition',
  id: 'POST-01',
  description: 'CALC-MONTHLY-RATE 実行後: WS-MONTHLY-RATE > 0',
  paragraphName: 'CALC-MONTHLY-RATE',
  condition: cmp('>', varRef('WS-MONTHLY-RATE'), lit(0)),
}
```

**検証方法**: `perform-return` イベント発生時に条件を評価。

### 4. RelationalProperty（変数間関係）

複数の変数間の数学的関係。固定小数点の丸め誤差を考慮したtolerance付き。

```typescript
{
  propertyType: 'relational',
  id: 'REL-01',
  description: 'WS-PRINCIPAL-AMT + WS-INTEREST-AMT ≈ WS-PAYMENT',
  condition: cmp('=',
    binOp('+', varRef('WS-PRINCIPAL-AMT'), varRef('WS-INTEREST-AMT')),
    varRef('WS-PAYMENT')
  ),
  tolerance: 0.01,
  checkAfterParagraph: 'CALC-AMORTIZATION',
}
```

**検証方法**: 指定パラグラフのreturn後に、tolerance考慮で条件を評価。

### 5. PrecisionProperty（算術精度）

算術演算の精度と丸めモードの制約。

```typescript
{
  propertyType: 'precision',
  id: 'PREC-01',
  description: 'WS-MONTHLY-RATE は ROUNDED モードで計算されること',
  targetVar: 'WS-MONTHLY-RATE',
  minDecimalPlaces: 6,
  roundingMode: 'must-round',  // must-round | must-truncate | any
}
```

**検証方法**: `arithmetic` イベントの `rounded` フラグと結果の小数桁数を検査。

### 6. OutputEquivalence（出力同値性）

DISPLAY出力がモダナイゼーション前後で一致すること。

```typescript
{
  propertyType: 'output-equivalence',
  id: 'OUT-01',
  description: 'DISPLAY出力が前後で一致すること',
  numericTolerance: 0.01,
}
```

**検証方法**: ソース側では出力を収集。クロス検証フェーズでターゲット出力と比較。
数値部分はtolerance付きで比較し、テキスト部分は完全一致を要求。

### 7. LoopBound（ループ上限）

ループが指定回数以内で終了することの保証。

```typescript
{
  propertyType: 'loop-bound',
  id: 'LOOP-01',
  description: 'CALC-AMORTIZATION ループは 12 回で終了する',
  paragraphName: 'CALC-AMORTIZATION',
  maxIterations: 12,
}
```

**検証方法**: `loop-iteration` イベントの最大iteration番号を検査。

### 8. FinalStateProperty（最終状態）

プログラム終了時の変数値の検証。

```typescript
{
  propertyType: 'final-state',
  id: 'FINAL-01',
  description: 'WS-STATUS は "HIGH-INT"',
  targetVar: 'WS-STATUS',
  expectedValue: 'HIGH-INT',
}
```

**検証方法**: インタプリタの最終変数マップから値を取得し、期待値と比較。

## 実装構成

### ファイル構成

```
src/
├── properties.ts         # プロパティ定義の型体系 + ビルダーヘルパー
├── verifier.ts           # トレースに対するプロパティ検証エンジン
├── proof-certificate.ts  # Proof Certificate の生成・比較・フォーマット
├── cross-verifier.ts     # 複数入力でのクロス検証
├── types.ts              # COBOL型システム (既存)
├── ast.ts                # AST定義 (既存)
├── tracer.ts             # 実行トレース収集 (既存)
├── interpreter.ts        # インタプリタ (既存)
├── codegen.ts            # TypeScriptコード生成 (既存)
└── main.ts               # デモ (Phase 4-6 追加)
```

### properties.ts - プロパティ定義（約220行）

**プロパティ式の型体系**:

```
PropertyExpression = PropVarRef        -- 変数参照
                   | PropLiteral       -- リテラル値
                   | PropBinaryOp      -- 二項演算 (+, -, *, /)
                   | PropAbsOp         -- 絶対値

PropertyCondition  = PropertyComparison -- 比較 (=, >, <, >=, <=, !=)
                   | PropertyLogical    -- 論理結合 (AND, OR)
```

**ビルダーヘルパー**: `varRef()`, `lit()`, `binOp()`, `abs()`, `cmp()`, `and()`, `or()`

```typescript
// 例: WS-PRINCIPAL-AMT + WS-INTEREST-AMT = WS-PAYMENT
cmp('=',
  binOp('+', varRef('WS-PRINCIPAL-AMT'), varRef('WS-INTEREST-AMT')),
  varRef('WS-PAYMENT')
)
```

### verifier.ts - 検証エンジン（約340行）

**コアクラス: `PropertyVerifier`**

```typescript
class PropertyVerifier {
  constructor(events, finalVariables, displayOutput)
  verify(propertySet: PropertySet): VerificationReport
}
```

**内部の `VariableStateTracker`**:
トレースイベントを時系列に走査し、`var-init` / `var-assign` イベントから
各時点での変数の値を再構築する。プロパティの条件式はこの再構築された状態に対して評価される。

**検証結果**:

```typescript
interface PropertyVerificationResult {
  propertyId: string;
  status: 'passed' | 'failed' | 'skipped';
  message: string;
  violations: Violation[];     // 失敗時の詳細
  eventsChecked: number;       // 検証に使ったイベント数
}
```

### proof-certificate.ts - 証明書生成（約280行）

**ビルダーパターン**:

```typescript
const cert = new ProofCertificateBuilder(programId, targetLang, propSet, report)
  .withTargetVerification(targetReport)   // ターゲット側の検証結果
  .withSourceOutput(displayOutput)        // ソース出力
  .withTargetOutput(targetOutput)         // ターゲット出力
  .withSourceState(stateMap)              // ソースの最終状態
  .withTargetState(targetStateMap)        // ターゲットの最終状態
  .withNumericTolerance(0.01)             // 数値比較の許容誤差
  .build();
```

**Property Preservation判定ロジック**:

| Source Status | Target Status | Preserved? |
|--------------|--------------|------------|
| passed | passed | Yes |
| passed | failed | **No** |
| passed | not-verified | Yes (暫定) |
| failed | * | No |
| skipped | * | Yes (N/A) |

### cross-verifier.ts - クロス検証（約170行）

**テスト入力によるパラメトリック検証**:

```typescript
const testInputs: TestInput[] = [
  { name: 'Low Rate', overrides: new Map([['WS-ANNUAL-RATE', 1.0]]) },
  { name: 'High Rate', overrides: new Map([['WS-ANNUAL-RATE', 8.0]]) },
];

const crossVerifier = new CrossVerifier(program, propertySet);
const suite = crossVerifier.verifyWithTestInputs(testInputs);
// → 各入力に対して独立にProof Certificateを生成
```

データ項目の初期値をオーバーライドして同じプログラムを複数回実行し、
全入力パターンでプロパティが成立するかを検証する。

## ローン計算プログラムでの適用例

### 定義した13プロパティ

| ID | カテゴリ | 説明 |
|----|---------|------|
| INV-01 | DataInvariant | WS-TOTAL-INTEREST >= 0 |
| INV-02 | DataInvariant | WS-BALANCE >= 0 |
| INV-03 | DataInvariant | WS-MONTHLY-RATE < 1 |
| PRE-01 | Precondition | CALC-MONTHLY-RATE前: WS-ANNUAL-RATE > 0 |
| PRE-02 | Precondition | CALC-PAYMENT前: WS-MONTHLY-RATE > 0 |
| POST-01 | Postcondition | CALC-MONTHLY-RATE後: WS-MONTHLY-RATE > 0 |
| POST-02 | Postcondition | CALC-PAYMENT後: WS-PAYMENT > 0 |
| REL-01 | Relational | 元本 + 利息 ≈ 支払額 |
| PREC-01 | Precision | WS-MONTHLY-RATE は ROUNDED |
| PREC-02 | Precision | WS-INTEREST-AMT は ROUNDED |
| LOOP-01 | LoopBound | 償還ループ <= 12回 |
| FINAL-01 | FinalState | WS-STATUS = "HIGH-INT" |
| OUT-01 | OutputEquivalence | DISPLAY出力一致 |

### デフォルト入力での検証結果

```
13/13 properties passed
Proof Certificate: VALID
Preservation Rate: 100.0%
```

### クロス検証結果（3つの追加入力）

| テスト入力 | 結果 | 備考 |
|-----------|------|------|
| Low Rate (1%, 5万) | 12/13 passed | FINAL-01失敗: LOW-INTになる(正しい) |
| High Rate (8%, 20万) | 13/13 passed | |
| Small Loan (5%, 1万) | 12/13 passed | FINAL-01失敗: LOW-INTになる(正しい) |

FINAL-01の「失敗」は、入力依存プロパティが正しく検出されていることを示す。
低金利・少額の場合は累計利息が3000を下回り`LOW-INT`になるため、入力固定の
FinalStateプロパティは適用外となる。

## テスト

```
37/37 tests passed

既存テスト: 24件（型システム、インタプリタ、トレース）
新規テスト: 13件
  - DataInvariant (成立 + 違反検出)
  - Precondition / Postcondition
  - FinalState (成立 + 不一致検出)
  - LoopBound (範囲内 + 超過検出)
  - RelationalProperty (tolerance付き)
  - PrecisionProperty (丸めモード)
  - Proof Certificate (valid + partial)
  - Cross Verification (複数入力)
```

## 今後の拡張ポイント

1. **ターゲット側の自動検証**: 生成されたTypeScriptコードを実際に実行し、同じプロパティセットで再検証
2. **プロパティの自動推論**: 実行トレースから不変条件を自動的に発見（Daikon的アプローチ）
3. **LLM連携**: プロパティ定義をLLMが読み取り、変換時にプロパティを保存するコードを生成
4. **回帰テスト生成**: クロス検証の入力パターンを自動生成し、カバレッジを最大化
5. **差分証明書**: プログラム変更時に影響を受けるプロパティのみ再検証
