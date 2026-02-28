/**
 * Lean IR Generator - COBOL AST → Lean 4 形式仕様への変換
 *
 * COBOLプログラムのASTをLean 4定理証明系の中間表現に変換する。
 * これにより、プログラムの意味論が形式的に定義され、
 * プロパティの証明が機械的に検証可能になる。
 *
 * 生成されるLean構造:
 * 1. State構造体 - プログラムの変数状態空間
 * 2. 初期状態定義 - DATA DIVISIONの形式化
 * 3. セマンティクス関数 - 各パラグラフの表示的意味論
 * 4. メイン実行関数 - PROCEDURE DIVISIONの形式化
 * 5. 型制約 - PIC句から導出される精度制約
 */

import {
  CobolProgram, Statement, Expression, Condition,
  DataItemDef, Paragraph,
} from './ast';
import { parsePic, PicClause } from './types';

// ============================================================
// Lean IR 型定義
// ============================================================

/** Lean 4 コード生成の結果 */
export interface LeanFormalization {
  /** Lean 4 ソースコード（完全なモジュール） */
  readonly leanSource: string;
  /** プログラムID */
  readonly programId: string;
  /** 状態構造体のフィールド一覧 */
  readonly stateFields: readonly LeanStateField[];
  /** 生成されたセマンティクス関数一覧 */
  readonly semanticFunctions: readonly LeanSemanticFunction[];
  /** 型制約一覧 */
  readonly typeConstraints: readonly LeanTypeConstraint[];
  /** 生成統計 */
  readonly stats: LeanGenerationStats;
}

/** 状態構造体のフィールド */
export interface LeanStateField {
  readonly cobolName: string;
  readonly leanName: string;
  readonly leanType: string;
  readonly pic: PicClause;
  readonly initialValue: string;
}

/** セマンティクス関数 */
export interface LeanSemanticFunction {
  readonly name: string;
  readonly paragraphName: string;
  readonly signature: string;
  readonly body: string;
}

/** 型制約（PIC句由来） */
export interface LeanTypeConstraint {
  readonly fieldName: string;
  readonly constraintType: 'range' | 'precision' | 'length';
  readonly leanExpr: string;
  readonly description: string;
}

/** 生成統計 */
export interface LeanGenerationStats {
  readonly totalFields: number;
  readonly totalFunctions: number;
  readonly totalConstraints: number;
  readonly totalLeanLines: number;
}

// ============================================================
// Lean IR Generator
// ============================================================

export class LeanIRGenerator {
  private program: CobolProgram;
  private stateFields: LeanStateField[] = [];
  private semanticFunctions: LeanSemanticFunction[] = [];
  private typeConstraints: LeanTypeConstraint[] = [];

  constructor(program: CobolProgram) {
    this.program = program;
  }

  /**
   * COBOLプログラムからLean 4形式仕様を生成する
   */
  generate(): LeanFormalization {
    // Phase 1: データ項目の分析
    this.analyzeDataItems(this.program.dataItems);

    // Phase 2: パラグラフのセマンティクス関数生成
    for (const para of this.program.paragraphs) {
      this.generateParagraphSemantics(para);
    }

    // Phase 3: Lean 4ソースコード組み立て
    const leanSource = this.assembleLeanSource();

    return {
      leanSource,
      programId: this.program.programId,
      stateFields: this.stateFields,
      semanticFunctions: this.semanticFunctions,
      typeConstraints: this.typeConstraints,
      stats: {
        totalFields: this.stateFields.length,
        totalFunctions: this.semanticFunctions.length,
        totalConstraints: this.typeConstraints.length,
        totalLeanLines: leanSource.split('\n').length,
      },
    };
  }

  // ============================================================
  // Phase 1: データ項目の分析とLean型マッピング
  // ============================================================

  private analyzeDataItems(items: DataItemDef[]): void {
    for (const item of items) {
      if (!item.pic) continue;
      const pic = parsePic(item.pic);
      const leanName = toLeanIdent(item.name);
      const leanType = this.picToLeanType(pic);
      const initialValue = this.formatLeanInitialValue(item, pic);

      this.stateFields.push({
        cobolName: item.name,
        leanName,
        leanType,
        pic,
        initialValue,
      });

      // PIC句から型制約を導出
      this.deriveTypeConstraints(leanName, item.name, pic);
    }
  }

  private picToLeanType(pic: PicClause): string {
    if (pic.category === 'numeric') {
      if (pic.decimalDigits > 0) {
        // 固定小数点 → Lean FixedPoint型（カスタム定義）
        return `FixedPoint ${pic.totalDigits} ${pic.decimalDigits}`;
      }
      if (pic.isSigned) {
        return 'Int';
      }
      return 'Nat';
    }
    // 英数字 → 固定長文字列
    return `BoundedString ${pic.size}`;
  }

  private formatLeanInitialValue(item: DataItemDef, pic: PicClause): string {
    if (pic.category === 'numeric') {
      const numVal = typeof item.value === 'number' ? item.value :
                     typeof item.value === 'string' ? parseFloat(item.value) : 0;
      if (pic.decimalDigits > 0) {
        return `FixedPoint.mk ${numVal.toFixed(pic.decimalDigits)} ${pic.decimalDigits}`;
      }
      return numVal.toString();
    }
    const strVal = item.value !== undefined ? String(item.value) : '';
    return `"${strVal}"`;
  }

  private deriveTypeConstraints(leanName: string, cobolName: string, pic: PicClause): void {
    if (pic.category === 'numeric') {
      const totalCapacity = pic.totalDigits + pic.decimalDigits;
      const maxVal = Math.pow(10, totalCapacity) - 1;
      const scaleFactor = Math.pow(10, pic.decimalDigits);
      const maxReal = maxVal / scaleFactor;

      // 範囲制約
      if (pic.isSigned) {
        this.typeConstraints.push({
          fieldName: leanName,
          constraintType: 'range',
          leanExpr: `∀ s : ProgramState, -${maxReal} ≤ s.${leanName}.val ∧ s.${leanName}.val ≤ ${maxReal}`,
          description: `${cobolName}: PIC ${pic.raw} → range [-${maxReal}, ${maxReal}]`,
        });
      } else {
        this.typeConstraints.push({
          fieldName: leanName,
          constraintType: 'range',
          leanExpr: `∀ s : ProgramState, 0 ≤ s.${leanName}.val ∧ s.${leanName}.val ≤ ${maxReal}`,
          description: `${cobolName}: PIC ${pic.raw} → range [0, ${maxReal}]`,
        });
      }

      // 精度制約
      if (pic.decimalDigits > 0) {
        this.typeConstraints.push({
          fieldName: leanName,
          constraintType: 'precision',
          leanExpr: `∀ s : ProgramState, s.${leanName}.scale = ${pic.decimalDigits}`,
          description: `${cobolName}: fixed-point scale = ${pic.decimalDigits}`,
        });
      }
    } else {
      // 長さ制約
      this.typeConstraints.push({
        fieldName: leanName,
        constraintType: 'length',
        leanExpr: `∀ s : ProgramState, s.${leanName}.length = ${pic.size}`,
        description: `${cobolName}: PIC ${pic.raw} → length = ${pic.size}`,
      });
    }
  }

  // ============================================================
  // Phase 2: パラグラフのセマンティクス関数生成
  // ============================================================

  private generateParagraphSemantics(para: Paragraph): void {
    const funcName = `sem_${toLeanIdent(para.name)}`;
    const body = this.generateStatementsLean(para.statements, '  ');

    const fn: LeanSemanticFunction = {
      name: funcName,
      paragraphName: para.name,
      signature: `def ${funcName} (s : ProgramState) : ProgramState :=`,
      body,
    };

    this.semanticFunctions.push(fn);
  }

  private generateStatementsLean(stmts: Statement[], indent: string): string {
    if (stmts.length === 0) return `${indent}s`;

    const lines: string[] = [];
    let currentState = 's';
    let stateCounter = 0;

    for (let i = 0; i < stmts.length; i++) {
      const stmt = stmts[i];
      const isLast = i === stmts.length - 1;
      const nextState = isLast ? '' : `s${++stateCounter}`;

      const stmtLean = this.generateStatementLean(stmt, currentState, nextState, indent, isLast);
      lines.push(stmtLean);

      if (!isLast) {
        currentState = nextState;
      }
    }

    return lines.join('\n');
  }

  private generateStatementLean(
    stmt: Statement, currentState: string, nextState: string,
    indent: string, isLast: boolean
  ): string {
    const binding = isLast ? '' : `let ${nextState} := `;

    switch (stmt.stmtType) {
      case 'move':
        return `${indent}${binding}{ ${currentState} with ${toLeanIdent(stmt.to)} := ${this.exprToLean(stmt.from, currentState)} }`;

      case 'add': {
        const target = stmt.giving || stmt.to;
        const addExprs = stmt.values.map(v => this.exprToLean(v, currentState)).join(' + ');
        const base = stmt.giving ? '' : `${currentState}.${toLeanIdent(target)} + `;
        const roundFn = stmt.rounded ? 'FixedPoint.round ' : '';
        return `${indent}${binding}{ ${currentState} with ${toLeanIdent(target)} := ${roundFn}(${base}${addExprs}) }`;
      }

      case 'subtract': {
        const target = stmt.giving || stmt.from;
        const subExprs = stmt.values.map(v => this.exprToLean(v, currentState)).join(' + ');
        const roundFn = stmt.rounded ? 'FixedPoint.round ' : '';
        return `${indent}${binding}{ ${currentState} with ${toLeanIdent(target)} := ${roundFn}(${currentState}.${toLeanIdent(stmt.from)} - (${subExprs})) }`;
      }

      case 'compute': {
        const roundFn = stmt.rounded ? 'FixedPoint.round ' : '';
        return `${indent}${binding}{ ${currentState} with ${toLeanIdent(stmt.target)} := ${roundFn}(${this.exprToLean(stmt.expression, currentState)}) }`;
      }

      case 'if':
        return this.generateIfLean(stmt, currentState, nextState, indent, isLast);

      case 'perform':
        return `${indent}${binding}sem_${toLeanIdent(stmt.paragraphName)} ${currentState}`;

      case 'perform-varying':
        return this.generatePerformVaryingLean(stmt, currentState, nextState, indent, isLast);

      case 'display':
        // DISPLAY doesn't change state in the pure model; side effects tracked separately
        return `${indent}${binding}${currentState} -- DISPLAY (side effect)`;

      case 'stop-run':
        return `${indent}${currentState}`;

      default:
        return `${indent}${binding}${currentState} -- ${stmt.stmtType} (not formalized)`;
    }
  }

  private generateIfLean(
    stmt: { condition: Condition; thenBlock: Statement[]; elseBlock: Statement[] },
    currentState: string, nextState: string,
    indent: string, isLast: boolean
  ): string {
    const binding = isLast ? '' : `let ${nextState} := `;
    const condLean = this.conditionToLean(stmt.condition, currentState);
    const thenBody = this.generateStatementsLean(stmt.thenBlock, indent + '  ');
    const elseBody = stmt.elseBlock.length > 0
      ? this.generateStatementsLean(stmt.elseBlock, indent + '  ')
      : `${indent}  ${currentState}`;

    return [
      `${indent}${binding}if ${condLean} then`,
      thenBody,
      `${indent}else`,
      elseBody,
    ].join('\n');
  }

  private generatePerformVaryingLean(
    stmt: {
      paragraphName: string; variable: string;
      from: Expression; by: Expression; until: Condition;
    },
    currentState: string, nextState: string,
    indent: string, isLast: boolean
  ): string {
    const binding = isLast ? '' : `let ${nextState} := `;
    const varName = toLeanIdent(stmt.variable);
    const fromVal = this.exprToLean(stmt.from, currentState);
    const byVal = this.exprToLean(stmt.by, currentState);
    const untilCond = this.conditionToLean(stmt.until, 'acc');
    const funcName = `sem_${toLeanIdent(stmt.paragraphName)}`;

    return [
      `${indent}${binding}-- PERFORM ${stmt.paragraphName} VARYING ${stmt.variable}`,
      `${indent}let initState := { ${currentState} with ${varName} := ${fromVal} }`,
      `${indent}loop_iterate initState (fun acc =>`,
      `${indent}  if ${untilCond} then acc`,
      `${indent}  else`,
      `${indent}    let acc' := ${funcName} acc`,
      `${indent}    { acc' with ${varName} := acc'.${varName} + ${byVal} })`,
    ].join('\n');
  }

  // ============================================================
  // 式・条件のLean変換
  // ============================================================

  private exprToLean(expr: Expression, stateVar: string): string {
    switch (expr.exprType) {
      case 'literal':
        if (typeof expr.value === 'string') return `"${expr.value}"`;
        if (Number.isInteger(expr.value)) return expr.value.toString();
        return `(${expr.value} : Float)`;
      case 'variable':
        return `${stateVar}.${toLeanIdent(expr.name)}`;
      case 'binary': {
        const left = this.exprToLean(expr.left, stateVar);
        const right = this.exprToLean(expr.right, stateVar);
        const op = expr.op === '**' ? '^' : expr.op;
        return `(${left} ${op} ${right})`;
      }
      case 'unary':
        return `(-${this.exprToLean(expr.operand, stateVar)})`;
    }
  }

  private conditionToLean(cond: Condition, stateVar: string): string {
    switch (cond.condType) {
      case 'comparison': {
        const left = this.exprToLean(cond.left, stateVar);
        const right = this.exprToLean(cond.right, stateVar);
        const opMap: Record<string, string> = {
          '=': '==', '>': '>', '<': '<', '>=': '≥', '<=': '≤', '!=': '≠',
        };
        return `(${left} ${opMap[cond.op] || cond.op} ${right})`;
      }
      case 'logical': {
        const left = this.conditionToLean(cond.left, stateVar);
        const right = this.conditionToLean(cond.right, stateVar);
        return cond.op === 'AND' ? `(${left} ∧ ${right})` : `(${left} ∨ ${right})`;
      }
      case 'not':
        return `¬${this.conditionToLean(cond.operand, stateVar)}`;
    }
  }

  // ============================================================
  // Phase 3: Lean 4ソースコード組み立て
  // ============================================================

  private assembleLeanSource(): string {
    const lines: string[] = [];
    const modName = toLeanIdent(this.program.programId);

    // モジュールヘッダー
    lines.push(`/-!`);
    lines.push(`  # Formal Specification: ${this.program.programId}`);
    lines.push(`  `);
    lines.push(`  Auto-generated Lean 4 formalization of COBOL program.`);
    lines.push(`  This module defines the denotational semantics of the program,`);
    lines.push(`  enabling machine-checkable proofs of program properties.`);
    lines.push(`  `);
    lines.push(`  ## Structure`);
    lines.push(`  - ProgramState: State space (variables)`);
    lines.push(`  - Semantic functions: Each paragraph's meaning`);
    lines.push(`  - Type constraints: PIC-clause-derived invariants`);
    lines.push(`  - Main execution: Complete program semantics`);
    lines.push(`-/`);
    lines.push('');
    lines.push(`namespace ${modName}`);
    lines.push('');

    // 基盤型定義
    lines.push('-- ============================================================');
    lines.push('-- Foundation Types (COBOL type system formalization)');
    lines.push('-- ============================================================');
    lines.push('');
    lines.push('/-- Fixed-point decimal with explicit scale (COBOL PIC 9(n)V9(m)) -/');
    lines.push('structure FixedPoint (intDigits : Nat) (decDigits : Nat) where');
    lines.push('  val : Float');
    lines.push('  scale : Nat := decDigits');
    lines.push('  h_scale : scale = decDigits := rfl');
    lines.push('  deriving Repr, BEq');
    lines.push('');
    lines.push('namespace FixedPoint');
    lines.push('  def mk (v : Float) (d : Nat) : FixedPoint d d := { val := v }');
    lines.push('  def round (fp : FixedPoint n m) : FixedPoint n m :=');
    lines.push('    let factor := Float.pow 10.0 m.toFloat');
    lines.push('    { fp with val := (fp.val * factor).round / factor }');
    lines.push('  instance : Add (FixedPoint n m) := ⟨fun a b => { a with val := a.val + b.val }⟩');
    lines.push('  instance : Sub (FixedPoint n m) := ⟨fun a b => { a with val := a.val - b.val }⟩');
    lines.push('  instance : Mul (FixedPoint n m) := ⟨fun a b => { a with val := a.val * b.val }⟩');
    lines.push('  instance : Div (FixedPoint n m) := ⟨fun a b => { a with val := a.val / b.val }⟩');
    lines.push('  instance : LE (FixedPoint n m) := ⟨fun a b => a.val ≤ b.val⟩');
    lines.push('  instance : LT (FixedPoint n m) := ⟨fun a b => a.val < b.val⟩');
    lines.push('end FixedPoint');
    lines.push('');
    lines.push('/-- Bounded-length string (COBOL PIC X(n)) -/');
    lines.push('structure BoundedString (maxLen : Nat) where');
    lines.push('  value : String');
    lines.push('  length : Nat := value.length');
    lines.push('  h_bound : length ≤ maxLen := by omega');
    lines.push('  deriving Repr, BEq');
    lines.push('');
    lines.push('/-- Loop iteration helper with fuel (guarantees termination) -/');
    lines.push('def loop_iterate (init : α) (step : α → α) (fuel : Nat := 10000) : α :=');
    lines.push('  match fuel with');
    lines.push('  | 0 => init');
    lines.push('  | n + 1 => loop_iterate (step init) step n');
    lines.push('');

    // 状態構造体
    lines.push('-- ============================================================');
    lines.push('-- Program State (DATA DIVISION formalization)');
    lines.push('-- ============================================================');
    lines.push('');
    lines.push('/-- Complete program state corresponding to WORKING-STORAGE SECTION -/');
    lines.push('structure ProgramState where');
    for (const field of this.stateFields) {
      lines.push(`  /-- ${field.cobolName} (PIC ${field.pic.raw}) -/`);
      lines.push(`  ${field.leanName} : ${field.leanType}`);
    }
    lines.push('  deriving Repr');
    lines.push('');

    // 初期状態
    lines.push('/-- Initial state from VALUE clauses -/');
    lines.push('def initialState : ProgramState := {');
    for (const field of this.stateFields) {
      lines.push(`  ${field.leanName} := ${field.initialValue},`);
    }
    lines.push('}');
    lines.push('');

    // 型制約（定理として宣言）
    lines.push('-- ============================================================');
    lines.push('-- Type Constraints (PIC clause invariants)');
    lines.push('-- ============================================================');
    lines.push('');
    for (const constraint of this.typeConstraints) {
      lines.push(`/-- ${constraint.description} -/`);
      lines.push(`axiom type_constraint_${constraint.fieldName} :`);
      lines.push(`  ${constraint.leanExpr}`);
      lines.push('');
    }

    // セマンティクス関数
    lines.push('-- ============================================================');
    lines.push('-- Semantic Functions (PROCEDURE DIVISION paragraphs)');
    lines.push('-- ============================================================');
    lines.push('');
    for (const fn of this.semanticFunctions) {
      lines.push(`/-- Paragraph: ${fn.paragraphName} -/`);
      lines.push(fn.signature);
      lines.push(fn.body);
      lines.push('');
    }

    // メイン実行関数
    lines.push('-- ============================================================');
    lines.push('-- Main Execution (complete program semantics)');
    lines.push('-- ============================================================');
    lines.push('');
    lines.push('/-- Complete program execution: initial state → final state -/');
    lines.push('def execute : ProgramState :=');
    const mainBody = this.generateStatementsLean(this.program.mainStatements, '  ');
    lines.push(mainBody.replace(/^  /, '  let s := initialState\n  '));
    lines.push('');

    lines.push(`end ${modName}`);

    return lines.join('\n');
  }
}

// ============================================================
// ユーティリティ
// ============================================================

/** COBOL名をLean識別子に変換 */
export function toLeanIdent(name: string): string {
  return name.toLowerCase().replace(/-/g, '_');
}
