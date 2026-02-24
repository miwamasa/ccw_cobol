/**
 * COBOL Subset AST - 型安全な構文木定義
 * 
 * サポートするCOBOLサブセット:
 * - DATA DIVISION (WORKING-STORAGE SECTION)
 * - PROCEDURE DIVISION
 * - MOVE, ADD, SUBTRACT, MULTIPLY, DIVIDE, COMPUTE
 * - IF/ELSE/END-IF
 * - PERFORM (simple, VARYING)
 * - DISPLAY
 * - STOP RUN
 */

// ============================================================
// DATA DIVISION AST
// ============================================================

/** データ項目定義 */
export interface DataItemDef {
  readonly nodeType: 'data-item';
  readonly level: number;           // 01, 05, 77, etc.
  readonly name: string;            // データ名
  readonly pic?: string;            // PIC句（グループ項目はなし）
  readonly value?: string | number; // VALUE句
  readonly children: DataItemDef[]; // 子項目（グループの場合）
}

// ============================================================
// PROCEDURE DIVISION AST - Discriminated Union
// ============================================================

export interface MoveStmt {
  readonly stmtType: 'move';
  readonly from: Expression;
  readonly to: string;    // 送り先変数名
}

export interface AddStmt {
  readonly stmtType: 'add';
  readonly values: Expression[];  // 加算する値リスト
  readonly to: string;            // 送り先変数名
  readonly giving?: string;       // GIVING変数名
  readonly rounded: boolean;
}

export interface SubtractStmt {
  readonly stmtType: 'subtract';
  readonly values: Expression[];
  readonly from: string;
  readonly giving?: string;
  readonly rounded: boolean;
}

export interface MultiplyStmt {
  readonly stmtType: 'multiply';
  readonly value: Expression;
  readonly by: Expression;
  readonly giving?: string;
  readonly rounded: boolean;
}

export interface DivideStmt {
  readonly stmtType: 'divide';
  readonly value: Expression;
  readonly by: Expression;
  readonly giving?: string;
  readonly remainder?: string;
  readonly rounded: boolean;
}

export interface ComputeStmt {
  readonly stmtType: 'compute';
  readonly target: string;
  readonly expression: Expression;
  readonly rounded: boolean;
}

export interface IfStmt {
  readonly stmtType: 'if';
  readonly condition: Condition;
  readonly thenBlock: Statement[];
  readonly elseBlock: Statement[];
}

export interface PerformStmt {
  readonly stmtType: 'perform';
  readonly paragraphName: string;
}

export interface PerformVaryingStmt {
  readonly stmtType: 'perform-varying';
  readonly paragraphName: string;
  readonly variable: string;
  readonly from: Expression;
  readonly by: Expression;
  readonly until: Condition;
}

export interface PerformTimesStmt {
  readonly stmtType: 'perform-times';
  readonly paragraphName: string;
  readonly times: Expression;
}

export interface DisplayStmt {
  readonly stmtType: 'display';
  readonly values: Expression[];
}

export interface StopRunStmt {
  readonly stmtType: 'stop-run';
}

export type Statement =
  | MoveStmt
  | AddStmt
  | SubtractStmt
  | MultiplyStmt
  | DivideStmt
  | ComputeStmt
  | IfStmt
  | PerformStmt
  | PerformVaryingStmt
  | PerformTimesStmt
  | DisplayStmt
  | StopRunStmt;

// ============================================================
// 式 (Expression) - Discriminated Union
// ============================================================

export interface LiteralExpr {
  readonly exprType: 'literal';
  readonly value: number | string;
}

export interface VariableExpr {
  readonly exprType: 'variable';
  readonly name: string;
}

export interface BinaryExpr {
  readonly exprType: 'binary';
  readonly op: '+' | '-' | '*' | '/' | '**';
  readonly left: Expression;
  readonly right: Expression;
}

export interface UnaryExpr {
  readonly exprType: 'unary';
  readonly op: '-';
  readonly operand: Expression;
}

export type Expression = LiteralExpr | VariableExpr | BinaryExpr | UnaryExpr;

// ============================================================
// 条件式 (Condition) - Discriminated Union
// ============================================================

export interface ComparisonCondition {
  readonly condType: 'comparison';
  readonly op: '=' | '>' | '<' | '>=' | '<=' | '!=';
  readonly left: Expression;
  readonly right: Expression;
}

export interface LogicalCondition {
  readonly condType: 'logical';
  readonly op: 'AND' | 'OR';
  readonly left: Condition;
  readonly right: Condition;
}

export interface NotCondition {
  readonly condType: 'not';
  readonly operand: Condition;
}

export type Condition = ComparisonCondition | LogicalCondition | NotCondition;

// ============================================================
// パラグラフとプログラム
// ============================================================

export interface Paragraph {
  readonly name: string;
  readonly statements: Statement[];
}

export interface CobolProgram {
  readonly programId: string;
  readonly dataItems: DataItemDef[];
  readonly paragraphs: Paragraph[];
  /** 最初に実行されるパラグラフ（またはメイン文のリスト） */
  readonly mainStatements: Statement[];
}
