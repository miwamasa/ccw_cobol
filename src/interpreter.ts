/**
 * Instrumented COBOL Interpreter - 型安全な計装付きインタプリタ
 * 
 * 設計方針:
 * 1. 全操作が型安全（FixedDecimal, Alphanumeric の区別を型レベルで強制）
 * 2. 全操作がトレースされる（暗黙変換、丸め、分岐すべて記録）
 * 3. COBOLの固定小数点演算を忠実に再現
 */

import {
  CobolValue, FixedDecimalValue, AlphanumericValue,
  PicClause, parsePic,
  makeFixedDecimal, makeAlphanumeric,
  decimalToNumber, formatCobolValue,
} from './types';
import {
  CobolProgram, Statement, Expression, Condition,
  DataItemDef, Paragraph, BinaryExpr,
} from './ast';
import { ExecutionTracer } from './tracer';

// ============================================================
// 変数ストレージ
// ============================================================

interface VariableSlot {
  pic: PicClause;
  value: CobolValue;
}

// ============================================================
// インタプリタ本体
// ============================================================

export class CobolInterpreter {
  private variables: Map<string, VariableSlot> = new Map();
  private paragraphs: Map<string, Paragraph> = new Map();
  private tracer: ExecutionTracer;
  private stopped: boolean = false;
  private displayOutput: string[] = [];

  constructor(tracer: ExecutionTracer) {
    this.tracer = tracer;
  }

  // ============================================================
  // プログラム実行
  // ============================================================

  execute(program: CobolProgram): ExecutionResult {
    this.tracer.recordProgramStart(program.programId, program.dataItems.length);

    // 1. データ項目の初期化
    this.initializeDataItems(program.dataItems);

    // 2. パラグラフの登録
    for (const para of program.paragraphs) {
      this.paragraphs.set(para.name, para);
    }

    // 3. メイン文の実行
    this.executeStatements(program.mainStatements);

    this.tracer.recordProgramEnd(program.programId);

    return {
      variables: new Map(
        [...this.variables.entries()].map(([k, v]) => [k, v.value])
      ),
      displayOutput: this.displayOutput,
      tracer: this.tracer,
    };
  }

  // ============================================================
  // データ初期化 - PIC句から型安全な値を生成
  // ============================================================

  private initializeDataItems(items: DataItemDef[]): void {
    for (const item of items) {
      if (item.pic) {
        const pic = parsePic(item.pic);
        let initialValue: CobolValue;

        if (pic.category === 'numeric') {
          const numVal = typeof item.value === 'number' ? item.value :
                         typeof item.value === 'string' ? parseFloat(item.value) : 0;
          initialValue = makeFixedDecimal(numVal, pic);
        } else {
          const strVal = item.value !== undefined ? String(item.value) : '';
          initialValue = makeAlphanumeric(strVal, pic.size);
        }

        this.variables.set(item.name, { pic, value: initialValue });
        this.tracer.recordVarInit(item.name, item.pic, initialValue);
      }

      // 子項目の初期化（グループ項目）
      if (item.children.length > 0) {
        this.initializeDataItems(item.children);
      }
    }
  }

  // ============================================================
  // 文の実行 (Statement Dispatch)
  // ============================================================

  private executeStatements(stmts: Statement[]): void {
    for (const stmt of stmts) {
      if (this.stopped) return;
      this.tracer.incrementStatementCount();
      this.executeStatement(stmt);
    }
  }

  private executeStatement(stmt: Statement): void {
    switch (stmt.stmtType) {
      case 'move':       return this.executeMOVE(stmt.from, stmt.to);
      case 'add':        return this.executeADD(stmt);
      case 'subtract':   return this.executeSUBTRACT(stmt);
      case 'multiply':   return this.executeMULTIPLY(stmt);
      case 'divide':     return this.executeDIVIDE(stmt);
      case 'compute':    return this.executeCOMPUTE(stmt);
      case 'if':         return this.executeIF(stmt);
      case 'perform':    return this.executePERFORM(stmt.paragraphName);
      case 'perform-varying': return this.executePERFORM_VARYING(stmt);
      case 'perform-times':   return this.executePERFORM_TIMES(stmt);
      case 'display':    return this.executeDISPLAY(stmt);
      case 'stop-run':   this.stopped = true; return;
    }
  }

  // ============================================================
  // MOVE文 - 暗黙の型変換を型安全に追跡
  // ============================================================

  private executeMOVE(fromExpr: Expression, toName: string): void {
    const targetSlot = this.variables.get(toName);
    if (!targetSlot) throw new Error(`Undefined variable: ${toName}`);

    const sourceValue = this.evaluateExpression(fromExpr);
    const previousValue = targetSlot.value;
    let conversionApplied = 'none';

    // 型安全な変換ロジック（COBOLの暗黙変換ルールを明示的に実装）
    let newValue: CobolValue;

    if (targetSlot.pic.category === 'numeric') {
      // 送り先が数値型
      const numericValue = this.coerceToNumber(sourceValue);
      newValue = makeFixedDecimal(numericValue, targetSlot.pic);
      if (typeof sourceValue === 'string') {
        conversionApplied = 'alphanumeric-to-numeric';
      } else {
        conversionApplied = 'numeric-move';
      }
    } else {
      // 送り先が英数字型
      const strValue = this.coerceToString(sourceValue);
      newValue = makeAlphanumeric(strValue, targetSlot.pic.size);
      if (typeof sourceValue === 'number') {
        conversionApplied = 'numeric-to-alphanumeric';
      } else {
        conversionApplied = 'alphanumeric-move';
      }
    }

    targetSlot.value = newValue;
    this.variables.set(toName, targetSlot);

    const sourceExprStr = this.expressionToString(fromExpr);
    this.tracer.recordVarAssign(toName, previousValue, newValue, {
      sourceExpr: sourceExprStr,
      sourceType: typeof sourceValue === 'number' ? 'numeric' : 'alphanumeric',
      conversionApplied,
    });
  }

  // ============================================================
  // 算術演算 - 固定小数点精度を完全追跡
  // ============================================================

  private executeADD(stmt: { values: Expression[]; to: string; giving?: string; rounded: boolean }): void {
    const targetName = stmt.giving || stmt.to;
    const targetSlot = this.variables.get(targetName);
    if (!targetSlot) throw new Error(`Undefined variable: ${targetName}`);

    let sum = stmt.giving ? 0 : this.getNumericValue(targetName);
    const operands: { name: string; value: string }[] = [];

    if (!stmt.giving) {
      operands.push({ name: targetName, value: sum.toString() });
    }

    for (const valExpr of stmt.values) {
      const val = this.evaluateNumericExpression(valExpr);
      sum += val;
      operands.push({ name: this.expressionToString(valExpr), value: val.toString() });
    }

    const { newValue, roundingDetail } = this.storeNumericResult(
      targetName, targetSlot, sum, stmt.rounded
    );

    this.tracer.recordArithmetic('ADD', operands, formatCobolValue(newValue),
      targetName, stmt.rounded, roundingDetail);
  }

  private executeSUBTRACT(stmt: { values: Expression[]; from: string; giving?: string; rounded: boolean }): void {
    const targetName = stmt.giving || stmt.from;
    const targetSlot = this.variables.get(targetName);
    if (!targetSlot) throw new Error(`Undefined variable: ${targetName}`);

    let result = this.getNumericValue(stmt.from);
    const operands: { name: string; value: string }[] = [
      { name: stmt.from, value: result.toString() }
    ];

    for (const valExpr of stmt.values) {
      const val = this.evaluateNumericExpression(valExpr);
      result -= val;
      operands.push({ name: this.expressionToString(valExpr), value: val.toString() });
    }

    const { newValue, roundingDetail } = this.storeNumericResult(
      targetName, targetSlot, result, stmt.rounded
    );

    this.tracer.recordArithmetic('SUBTRACT', operands, formatCobolValue(newValue),
      targetName, stmt.rounded, roundingDetail);
  }

  private executeMULTIPLY(stmt: { value: Expression; by: Expression; giving?: string; rounded: boolean }): void {
    const val1 = this.evaluateNumericExpression(stmt.value);
    const val2 = this.evaluateNumericExpression(stmt.by);
    const result = val1 * val2;

    const targetName = stmt.giving || this.expressionToString(stmt.value);
    const targetSlot = this.variables.get(targetName);
    if (!targetSlot) throw new Error(`Undefined variable: ${targetName}`);

    const operands = [
      { name: this.expressionToString(stmt.value), value: val1.toString() },
      { name: this.expressionToString(stmt.by), value: val2.toString() },
    ];

    const { newValue, roundingDetail } = this.storeNumericResult(
      targetName, targetSlot, result, stmt.rounded
    );

    this.tracer.recordArithmetic('MULTIPLY', operands, formatCobolValue(newValue),
      targetName, stmt.rounded, roundingDetail);
  }

  private executeDIVIDE(stmt: { value: Expression; by: Expression; giving?: string; remainder?: string; rounded: boolean }): void {
    const val1 = this.evaluateNumericExpression(stmt.value);
    const val2 = this.evaluateNumericExpression(stmt.by);

    if (val2 === 0) throw new Error('Division by zero');
    const result = val1 / val2;

    const targetName = stmt.giving || this.expressionToString(stmt.value);
    const targetSlot = this.variables.get(targetName);
    if (!targetSlot) throw new Error(`Undefined variable: ${targetName}`);

    const operands = [
      { name: this.expressionToString(stmt.value), value: val1.toString() },
      { name: this.expressionToString(stmt.by), value: val2.toString() },
    ];

    const { newValue, roundingDetail } = this.storeNumericResult(
      targetName, targetSlot, result, stmt.rounded
    );

    // REMAINDER処理
    if (stmt.remainder) {
      const remainderSlot = this.variables.get(stmt.remainder);
      if (remainderSlot) {
        const quotient = Math.trunc(val1 / val2);
        const rem = val1 - quotient * val2;
        this.storeNumericResult(stmt.remainder, remainderSlot, rem, false);
      }
    }

    this.tracer.recordArithmetic('DIVIDE', operands, formatCobolValue(newValue),
      targetName, stmt.rounded, roundingDetail);
  }

  private executeCOMPUTE(stmt: { target: string; expression: Expression; rounded: boolean }): void {
    const targetSlot = this.variables.get(stmt.target);
    if (!targetSlot) throw new Error(`Undefined variable: ${stmt.target}`);

    const result = this.evaluateNumericExpression(stmt.expression);
    const exprStr = this.expressionToString(stmt.expression);

    const { newValue, roundingDetail } = this.storeNumericResult(
      stmt.target, targetSlot, result, stmt.rounded
    );

    this.tracer.recordArithmetic('COMPUTE', [
      { name: exprStr, value: result.toString() },
    ], formatCobolValue(newValue), stmt.target, stmt.rounded, roundingDetail);
  }

  /** 数値結果を変数に格納（丸め処理と追跡を含む） */
  private storeNumericResult(
    varName: string,
    slot: VariableSlot,
    rawResult: number,
    rounded: boolean
  ): { newValue: FixedDecimalValue; roundingDetail?: { rawResult: string; roundedResult: string; truncatedDigits: number } } {
    const pic = slot.pic;
    const scale = pic.decimalDigits;
    const factor = 10 ** scale;
    
    let roundingDetail: { rawResult: string; roundedResult: string; truncatedDigits: number } | undefined;

    let storedResult: number;
    if (rounded) {
      // ROUNDED: 四捨五入
      storedResult = Math.round(rawResult * factor) / factor;
      if (storedResult !== Math.trunc(rawResult * factor) / factor) {
        roundingDetail = {
          rawResult: rawResult.toFixed(scale + 4),
          roundedResult: storedResult.toFixed(scale),
          truncatedDigits: scale,
        };
      }
    } else {
      // デフォルト: 切り捨て（COBOLのTRUNCATION）
      storedResult = Math.trunc(rawResult * factor) / factor;
      if (storedResult !== rawResult) {
        roundingDetail = {
          rawResult: rawResult.toFixed(scale + 4),
          roundedResult: storedResult.toFixed(scale),
          truncatedDigits: scale,
        };
      }
    }

    const previousValue = slot.value;
    const newValue = makeFixedDecimal(storedResult, pic);
    slot.value = newValue;
    this.variables.set(varName, slot);

    this.tracer.recordVarAssign(varName, previousValue, newValue, {
      sourceExpr: `arithmetic result: ${rawResult}`,
      sourceType: 'numeric',
      conversionApplied: rounded ? 'rounded' : (roundingDetail ? 'truncation' : 'none'),
    });

    return { newValue, roundingDetail };
  }

  // ============================================================
  // IF文 - 分岐パスを完全追跡
  // ============================================================

  private executeIF(stmt: { condition: Condition; thenBlock: Statement[]; elseBlock: Statement[] }): void {
    const condDetails: { part: string; value: string }[] = [];
    const result = this.evaluateCondition(stmt.condition, condDetails);
    const branchTaken = result ? 'then' : 'else';

    this.tracer.recordBranch(
      this.conditionToString(stmt.condition),
      result,
      branchTaken,
      condDetails
    );

    if (result) {
      this.executeStatements(stmt.thenBlock);
    } else {
      this.executeStatements(stmt.elseBlock);
    }
  }

  // ============================================================
  // PERFORM文 - 呼び出しシーケンスを追跡
  // ============================================================

  private executePERFORM(paragraphName: string): void {
    const para = this.paragraphs.get(paragraphName);
    if (!para) throw new Error(`Undefined paragraph: ${paragraphName}`);

    this.tracer.recordPerformCall(paragraphName);
    this.executeStatements(para.statements);
    this.tracer.recordPerformReturn(paragraphName);
  }

  private executePERFORM_VARYING(stmt: {
    paragraphName: string; variable: string;
    from: Expression; by: Expression; until: Condition;
  }): void {
    const para = this.paragraphs.get(stmt.paragraphName);
    if (!para) throw new Error(`Undefined paragraph: ${stmt.paragraphName}`);

    const fromVal = this.evaluateNumericExpression(stmt.from);
    const byVal = this.evaluateNumericExpression(stmt.by);

    // 初期値設定
    this.setNumericVariable(stmt.variable, fromVal);
    let iteration = 0;
    const MAX_ITERATIONS = 10000; // 安全制限

    while (iteration < MAX_ITERATIONS) {
      // UNTIL条件チェック（先頭チェック）
      const condDetails: { part: string; value: string }[] = [];
      if (this.evaluateCondition(stmt.until, condDetails)) break;

      iteration++;
      const currentVal = this.getNumericValue(stmt.variable);
      this.tracer.recordLoopIteration(stmt.paragraphName, stmt.variable, currentVal.toString(), iteration);
      this.tracer.recordPerformCall(stmt.paragraphName);
      this.executeStatements(para.statements);
      this.tracer.recordPerformReturn(stmt.paragraphName);

      // BY分のインクリメント
      const newVal = this.getNumericValue(stmt.variable) + byVal;
      this.setNumericVariable(stmt.variable, newVal);
    }
  }

  private executePERFORM_TIMES(stmt: { paragraphName: string; times: Expression }): void {
    const para = this.paragraphs.get(stmt.paragraphName);
    if (!para) throw new Error(`Undefined paragraph: ${stmt.paragraphName}`);

    const times = Math.trunc(this.evaluateNumericExpression(stmt.times));
    for (let i = 0; i < times; i++) {
      this.tracer.recordPerformCall(stmt.paragraphName);
      this.executeStatements(para.statements);
      this.tracer.recordPerformReturn(stmt.paragraphName);
    }
  }

  // ============================================================
  // DISPLAY文
  // ============================================================

  private executeDISPLAY(stmt: { values: Expression[] }): void {
    const parts = stmt.values.map(v => {
      const val = this.evaluateExpression(v);
      return typeof val === 'number' ? val.toString() : val;
    });
    const output = parts.join('');
    this.displayOutput.push(output);
    this.tracer.recordDisplay(output);
  }

  // ============================================================
  // 式の評価
  // ============================================================

  private evaluateExpression(expr: Expression): number | string {
    switch (expr.exprType) {
      case 'literal':
        return expr.value;
      case 'variable': {
        const slot = this.variables.get(expr.name);
        if (!slot) throw new Error(`Undefined variable: ${expr.name}`);
        if (slot.value.kind === 'fixed-decimal') return decimalToNumber(slot.value);
        if (slot.value.kind === 'alphanumeric') return slot.value.bytes.trimEnd();
        throw new Error(`Cannot evaluate group item: ${expr.name}`);
      }
      case 'binary':
        return this.evaluateBinaryExpr(expr);
      case 'unary':
        return -(this.evaluateNumericExpression(expr.operand));
    }
  }

  private evaluateNumericExpression(expr: Expression): number {
    const val = this.evaluateExpression(expr);
    return this.coerceToNumber(val);
  }

  private evaluateBinaryExpr(expr: BinaryExpr): number {
    const left = this.evaluateNumericExpression(expr.left);
    const right = this.evaluateNumericExpression(expr.right);
    switch (expr.op) {
      case '+': return left + right;
      case '-': return left - right;
      case '*': return left * right;
      case '/': return right !== 0 ? left / right : 0;
      case '**': return Math.pow(left, right);
    }
  }

  // ============================================================
  // 条件式の評価
  // ============================================================

  private evaluateCondition(
    cond: Condition,
    details: { part: string; value: string }[]
  ): boolean {
    switch (cond.condType) {
      case 'comparison': {
        const left = this.evaluateExpression(cond.left);
        const right = this.evaluateExpression(cond.right);
        const leftNum = typeof left === 'number' ? left : parseFloat(left) || 0;
        const rightNum = typeof right === 'number' ? right : parseFloat(right) || 0;

        let result: boolean;
        // 数値比較を優先（COBOLのルール）
        switch (cond.op) {
          case '=':  result = leftNum === rightNum; break;
          case '>':  result = leftNum > rightNum; break;
          case '<':  result = leftNum < rightNum; break;
          case '>=': result = leftNum >= rightNum; break;
          case '<=': result = leftNum <= rightNum; break;
          case '!=': result = leftNum !== rightNum; break;
        }

        details.push({
          part: `${this.expressionToString(cond.left)} ${cond.op} ${this.expressionToString(cond.right)}`,
          value: `${left} ${cond.op} ${right} => ${result}`,
        });
        return result;
      }
      case 'logical': {
        const leftResult = this.evaluateCondition(cond.left, details);
        const rightResult = this.evaluateCondition(cond.right, details);
        return cond.op === 'AND' ? leftResult && rightResult : leftResult || rightResult;
      }
      case 'not':
        return !this.evaluateCondition(cond.operand, details);
    }
  }

  // ============================================================
  // ヘルパーメソッド
  // ============================================================

  private coerceToNumber(val: number | string): number {
    if (typeof val === 'number') return val;
    const parsed = parseFloat(val);
    return isNaN(parsed) ? 0 : parsed;
  }

  private coerceToString(val: number | string): string {
    return typeof val === 'string' ? val : val.toString();
  }

  private getNumericValue(varName: string): number {
    const slot = this.variables.get(varName);
    if (!slot) throw new Error(`Undefined variable: ${varName}`);
    if (slot.value.kind === 'fixed-decimal') return decimalToNumber(slot.value);
    return 0;
  }

  private setNumericVariable(varName: string, value: number): void {
    const slot = this.variables.get(varName);
    if (!slot) throw new Error(`Undefined variable: ${varName}`);
    const prev = slot.value;
    slot.value = makeFixedDecimal(value, slot.pic);
    this.variables.set(varName, slot);
    this.tracer.recordVarAssign(varName, prev, slot.value, {
      sourceExpr: `direct set: ${value}`,
      sourceType: 'numeric',
      conversionApplied: 'none',
    });
  }

  private expressionToString(expr: Expression): string {
    switch (expr.exprType) {
      case 'literal': return typeof expr.value === 'string' ? `"${expr.value}"` : expr.value.toString();
      case 'variable': return expr.name;
      case 'binary': return `(${this.expressionToString(expr.left)} ${expr.op} ${this.expressionToString(expr.right)})`;
      case 'unary': return `(-${this.expressionToString(expr.operand)})`;
    }
  }

  private conditionToString(cond: Condition): string {
    switch (cond.condType) {
      case 'comparison':
        return `${this.expressionToString(cond.left)} ${cond.op} ${this.expressionToString(cond.right)}`;
      case 'logical':
        return `(${this.conditionToString(cond.left)} ${cond.op} ${this.conditionToString(cond.right)})`;
      case 'not':
        return `NOT (${this.conditionToString(cond.operand)})`;
    }
  }
}

// ============================================================
// 実行結果
// ============================================================

export interface ExecutionResult {
  variables: Map<string, CobolValue>;
  displayOutput: string[];
  tracer: ExecutionTracer;
}
