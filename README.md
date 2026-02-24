# COBOL Instrumented Interpreter - Proof of Concept

## 概要

**「型安全なCOBOLインタプリタを構築し、実行トレースを収集し、そのトレースからモダンコードを生成する」** というCOBOLモダナイゼーション手法のPOCです。

### 核心的アイデア

```
┌─────────────────┐    ┌──────────────────────┐    ┌─────────────────┐
│  COBOL Source    │───▶│  Type-Safe Runtime    │───▶│  Execution      │
│  (既存資産)       │    │  (TypeScript/Rust)    │    │  Traces         │
└─────────────────┘    │                      │    │  (構造化ログ)    │
                       │  - Discriminated Union│    └────────┬────────┘
                       │  - Fixed-Point Math   │             │
                       │  - Instrumented       │             ▼
                       └──────────────────────┘    ┌─────────────────┐
                                ▲                   │  Modern Code    │
                                │                   │  Generator      │
                                │                   │  (LLM / Rules)  │
                       「ランタイム自体が           └─────────────────┘
                         実行可能な仕様書」                  │
                                                           ▼
                                                  ┌─────────────────┐
                                                  │  TypeScript /   │
                                                  │  Java / etc.    │
                                                  └─────────────────┘
```

## 実証した3つの重要な洞察

### 1. 型安全ランタイムがCOBOLの暗黙的型を明示化する

```typescript
// COBOLのPIC句 → TypeScriptのDiscriminated Union
type CobolValue = FixedDecimalValue | AlphanumericValue | GroupValue;

interface FixedDecimalValue {
  kind: 'fixed-decimal';
  rawValue: bigint;      // 内部整数表現
  scale: number;         // 小数桁数
  integerDigits: number; // 整数桁数
  signed: boolean;       // 符号
}
```

PIC `S9(7)V99` のような暗黙的な型情報が、明示的なフィールドとして表現される。

### 2. 実行トレースが「例による仕様」になる

```json
{
  "eventType": "arithmetic",
  "operation": "COMPUTE",
  "operands": [{"name": "WS-BALANCE * WS-MONTHLY-RATE", "value": "291.7"}],
  "result": "291.70",
  "targetVar": "WS-INTEREST-AMT",
  "rounded": true,
  "roundingDetail": {
    "rawResult": "291.7000",
    "roundedResult": "291.70",
    "truncatedDigits": 2
  }
}
```

静的解析では「コードが何をし得るか」しかわからないが、トレースは「コードが実際に何をしたか」を示す。

### 3. ランタイム自体が「実行可能な仕様書」になる

型安全インタプリタのコード自体がCOBOLセマンティクスの正確な記述であり、変換先言語の参照実装であり、正確性検証のテストオラクルとなる。

## プロジェクト構造

```
cobol-poc/
├── src/
│   ├── types.ts          # COBOL型システム（Discriminated Union, PIC句パーサー）
│   ├── ast.ts            # AST定義（文・式・条件のUnion型）
│   ├── tracer.ts         # 実行トレース収集器（10種のイベント型）
│   ├── interpreter.ts    # 計装付きインタプリタ（型安全な実行エンジン）
│   ├── codegen.ts        # トレース→TypeScriptコード生成器
│   └── main.ts           # サンプルCOBOL（ローン利息計算）とデモ
├── tests/
│   └── run-tests.ts      # テストスイート（24テストケース）
├── tsconfig.json         # TypeScript strict mode
└── package.json
```

## サポートするCOBOLサブセット

| 機能 | サポート状況 |
|------|-------------|
| PIC句 (9, X, V, S) | ✅ |
| MOVE（暗黙的型変換追跡） | ✅ |
| ADD / SUBTRACT / MULTIPLY / DIVIDE | ✅ |
| COMPUTE（複合式） | ✅ |
| ROUNDED / TRUNCATION | ✅ |
| IF / ELSE / END-IF | ✅ |
| PERFORM（単純呼び出し） | ✅ |
| PERFORM VARYING | ✅ |
| PERFORM TIMES | ✅ |
| DISPLAY | ✅ |
| STOP RUN | ✅ |

## 実行方法

```bash
# インストール
npm install

# ビルド＆実行
npm start

# テスト実行
npm test
```

## テストスイート (24ケース)

| カテゴリ | テスト数 | 内容 |
|---------|---------|------|
| PIC句パーサー | 5 | 数値/英数字/符号/小数点のPIC解析 |
| 固定小数点値 | 4 | 精度、切り捨て、ゼロ、フォーマット |
| 英数字値 | 2 | パディング、切り捨て |
| MOVE文 | 3 | 数値転送、文字列転送、型変換追跡 |
| 算術演算 | 3 | ADD、COMPUTE ROUNDED、丸めトレース |
| IF文 | 2 | 分岐実行、分岐トレース記録 |
| PERFORM VARYING | 1 | ループ回数・値の正確性 |
| トレース収集 | 3 | 開始/終了、初期化、サマリー |
| 統合テスト | 1 | ローン月利計算の精度 |

## 収集するトレースイベント（10種類）

| イベント型 | 記録内容 |
|-----------|---------|
| `program-start` | プログラム開始、データ項目数 |
| `program-end` | プログラム終了、総実行文数 |
| `var-init` | 変数初期化（PIC句、初期値、型） |
| `var-assign` | 変数代入（前値、新値、型変換情報） |
| `arithmetic` | 算術演算（演算子、被演算子、結果、丸め詳細） |
| `branch` | 分岐決定（条件式、評価結果、実行パス） |
| `perform-call` | パラグラフ呼び出し（深度） |
| `perform-return` | パラグラフ復帰 |
| `loop-iteration` | ループ反復（カウンタ値、反復回数） |
| `display` | 出力テキスト |

## 生成されるコードの特徴

POCのコード生成器は以下の分析をトレースから導出します：

1. **型推論**: 算術演算に使われた変数 → `number`型、それ以外 → `string`型
2. **精度要件**: 丸めが検出された変数 → BigDecimalの必要性を警告
3. **分岐カバレッジ**: 未実行分岐の検出 → テストデータ追加の必要性を警告
4. **暗黙的型変換**: MOVE時の型変換を全て検出・報告
5. **パラグラフ → 関数**: 呼び出し回数の統計付きで変換

## 実プロダクトへの拡張ポイント

このPOCから実プロダクトに向けて：

- **COBOLパーサーの追加**: テキストのCOBOLソースからASTを構築
- **LLM統合**: トレース + AST + ランタイムコードをLLMに入力してコード生成
- **外部環境モック**: CICS/DB2/MQのインターフェース抽象化
- **カバレッジ駆動テスト生成**: 未到達パスに対するテストデータの自動生成
- **差分実行**: オリジナルCOBOL vs 生成コードの出力比較
