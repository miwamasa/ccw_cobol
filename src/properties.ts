/**
 * Property Definition System - Proof-Carrying Modernization
 *
 * COBOLプログラムに対して定義可能なプロパティ（制約・不変条件）の型体系。
 * これらのプロパティは元プログラムに対して定義され、
 * モダナイゼーション後のコードでも保存されることを検証する。
 *
 * プロパティのカテゴリ:
 * 1. DataInvariant    - 変数に対する不変条件 (e.g. balance >= 0)
 * 2. Precondition     - パラグラフ実行前の事前条件
 * 3. Postcondition    - パラグラフ実行後の事後条件
 * 4. RelationalProperty - 変数間の関係 (e.g. principal + interest = payment)
 * 5. PrecisionProperty - 算術精度の制約
 * 6. OutputEquivalence - DISPLAY出力の同値性
 * 7. LoopBound        - ループの終了保証（上限反復回数）
 */

// ============================================================
// 値式: プロパティ内で変数値を参照するための式
// ============================================================

/** プロパティ式: 変数参照 */
export interface PropVarRef {
  readonly kind: 'var-ref';
  readonly varName: string;
}

/** プロパティ式: リテラル値 */
export interface PropLiteral {
  readonly kind: 'literal';
  readonly value: number | string;
}

/** プロパティ式: 二項演算 */
export interface PropBinaryOp {
  readonly kind: 'binary-op';
  readonly op: '+' | '-' | '*' | '/';
  readonly left: PropertyExpression;
  readonly right: PropertyExpression;
}

/** プロパティ式: 絶対値 */
export interface PropAbsOp {
  readonly kind: 'abs';
  readonly operand: PropertyExpression;
}

export type PropertyExpression = PropVarRef | PropLiteral | PropBinaryOp | PropAbsOp;

// ============================================================
// 比較条件: プロパティの成立条件
// ============================================================

export interface PropertyComparison {
  readonly op: '=' | '>' | '<' | '>=' | '<=' | '!=';
  readonly left: PropertyExpression;
  readonly right: PropertyExpression;
}

export interface PropertyLogical {
  readonly logicalOp: 'AND' | 'OR';
  readonly conditions: PropertyCondition[];
}

export type PropertyCondition = PropertyComparison | PropertyLogical;

// ============================================================
// プロパティ定義 (Discriminated Union)
// ============================================================

/**
 * DataInvariant: 全実行ステップで成立する変数の不変条件
 * 例: "WS-BALANCE は常に 0 以上"
 */
export interface DataInvariant {
  readonly propertyType: 'data-invariant';
  readonly id: string;
  readonly description: string;
  /** 対象変数名 */
  readonly targetVar: string;
  /** 成立条件 */
  readonly condition: PropertyCondition;
  /** 条件チェックのタイミング */
  readonly checkAt: 'every-assignment' | 'after-paragraph' | 'at-end';
}

/**
 * Precondition: パラグラフ呼び出し前に成立すべき条件
 * 例: "CALC-MONTHLY-RATE 呼び出し前に WS-ANNUAL-RATE > 0"
 */
export interface Precondition {
  readonly propertyType: 'precondition';
  readonly id: string;
  readonly description: string;
  /** 対象パラグラフ */
  readonly paragraphName: string;
  /** 事前条件 */
  readonly condition: PropertyCondition;
}

/**
 * Postcondition: パラグラフ実行後に成立すべき条件
 * 例: "CALC-MONTHLY-RATE 実行後に WS-MONTHLY-RATE > 0"
 */
export interface Postcondition {
  readonly propertyType: 'postcondition';
  readonly id: string;
  readonly description: string;
  /** 対象パラグラフ */
  readonly paragraphName: string;
  /** 事後条件 */
  readonly condition: PropertyCondition;
}

/**
 * RelationalProperty: 変数間の関係が常に成立すること
 * 例: "WS-PRINCIPAL-AMT + WS-INTEREST-AMT = WS-PAYMENT"
 */
export interface RelationalProperty {
  readonly propertyType: 'relational';
  readonly id: string;
  readonly description: string;
  /** 関係式の条件 */
  readonly condition: PropertyCondition;
  /** 許容誤差（固定小数点の丸め誤差考慮） */
  readonly tolerance: number;
  /** チェックするタイミング */
  readonly checkAfterParagraph: string;
}

/**
 * PrecisionProperty: 算術精度の保証
 * 例: "WS-MONTHLY-RATE は小数点以下6桁の精度を保つ"
 */
export interface PrecisionProperty {
  readonly propertyType: 'precision';
  readonly id: string;
  readonly description: string;
  /** 対象変数 */
  readonly targetVar: string;
  /** 最小精度（小数桁数） */
  readonly minDecimalPlaces: number;
  /** 丸めモードの制約 */
  readonly roundingMode: 'must-round' | 'must-truncate' | 'any';
}

/**
 * OutputEquivalence: DISPLAY出力が同一であること
 * 元プログラムと変換後プログラムのDISPLAY出力を比較する。
 */
export interface OutputEquivalence {
  readonly propertyType: 'output-equivalence';
  readonly id: string;
  readonly description: string;
  /** 出力行番号（0-indexed, undefinedなら全行） */
  readonly lineIndices?: readonly number[];
  /** 数値部分の許容誤差 */
  readonly numericTolerance: number;
}

/**
 * LoopBound: ループの反復回数の上限保証
 */
export interface LoopBound {
  readonly propertyType: 'loop-bound';
  readonly id: string;
  readonly description: string;
  /** 対象パラグラフ（ループ本体） */
  readonly paragraphName: string;
  /** 最大反復回数 */
  readonly maxIterations: number;
}

/**
 * FinalStateProperty: プログラム終了時の最終状態に対する条件
 */
export interface FinalStateProperty {
  readonly propertyType: 'final-state';
  readonly id: string;
  readonly description: string;
  /** 対象変数名 */
  readonly targetVar: string;
  /** 期待値（exactまたはtolerance付き） */
  readonly expectedValue: number | string;
  /** 数値の場合の許容誤差 */
  readonly tolerance?: number;
}

/** 全プロパティのUnion型 */
export type Property =
  | DataInvariant
  | Precondition
  | Postcondition
  | RelationalProperty
  | PrecisionProperty
  | OutputEquivalence
  | LoopBound
  | FinalStateProperty;

// ============================================================
// PropertySet: プログラムに紐づくプロパティ集合
// ============================================================

export interface PropertySet {
  readonly programId: string;
  readonly properties: readonly Property[];
  /** プロパティセットのバージョン（変更追跡用） */
  readonly version: string;
  /** 作成日時 */
  readonly createdAt: string;
}

// ============================================================
// ビルダーヘルパー: プロパティを簡潔に定義するための関数群
// ============================================================

/** 変数参照 */
export function varRef(name: string): PropVarRef {
  return { kind: 'var-ref', varName: name };
}

/** リテラル値 */
export function lit(value: number | string): PropLiteral {
  return { kind: 'literal', value };
}

/** 二項演算 */
export function binOp(op: '+' | '-' | '*' | '/', left: PropertyExpression, right: PropertyExpression): PropBinaryOp {
  return { kind: 'binary-op', op, left, right };
}

/** 絶対値 */
export function abs(operand: PropertyExpression): PropAbsOp {
  return { kind: 'abs', operand };
}

/** 比較条件 */
export function cmp(op: PropertyComparison['op'], left: PropertyExpression, right: PropertyExpression): PropertyComparison {
  return { op, left, right };
}

/** 論理AND */
export function and(...conditions: PropertyCondition[]): PropertyLogical {
  return { logicalOp: 'AND', conditions };
}

/** 論理OR */
export function or(...conditions: PropertyCondition[]): PropertyLogical {
  return { logicalOp: 'OR', conditions };
}
