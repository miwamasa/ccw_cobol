/**
 * Execution Tracer - 実行トレース収集器
 * 
 * インタプリタの全操作を構造化ログとして記録する。
 * このトレースが後段のコード生成への入力となる。
 * 
 * 記録する情報:
 * 1. 変数の型遷移（MOVEによる暗黙変換を含む）
 * 2. 分岐の実行パス（IF文のどちらが実行されたか）
 * 3. 算術演算の入出力（固定小数点の丸め挙動を含む）
 * 4. パラグラフの呼び出しシーケンス
 * 5. PERFORM VARYINGのループ回数と変数遷移
 */

import { CobolValue, formatCobolValue } from './types';

// ============================================================
// トレースイベント型 (Discriminated Union)
// ============================================================

export interface VarInitEvent {
  readonly eventType: 'var-init';
  readonly timestamp: number;
  readonly varName: string;
  readonly picClause: string;
  readonly initialValue: string;
  readonly cobolType: string;      // 'fixed-decimal' | 'alphanumeric' | 'group'
}

export interface VarAssignEvent {
  readonly eventType: 'var-assign';
  readonly timestamp: number;
  readonly varName: string;
  readonly previousValue: string;
  readonly newValue: string;
  readonly previousType: string;
  readonly newType: string;
  /** MOVE元の情報（暗黙変換の追跡） */
  readonly sourceInfo?: {
    readonly sourceExpr: string;
    readonly sourceType: string;
    readonly conversionApplied: string; // e.g. 'numeric-to-alphanumeric', 'truncation'
  };
}

export interface ArithmeticEvent {
  readonly eventType: 'arithmetic';
  readonly timestamp: number;
  readonly operation: string;      // ADD, SUBTRACT, MULTIPLY, DIVIDE, COMPUTE
  readonly operands: readonly { name: string; value: string }[];
  readonly result: string;
  readonly targetVar: string;
  readonly rounded: boolean;
  /** 丸めが発生した場合の詳細 */
  readonly roundingDetail?: {
    readonly rawResult: string;
    readonly roundedResult: string;
    readonly truncatedDigits: number;
  };
}

export interface BranchEvent {
  readonly eventType: 'branch';
  readonly timestamp: number;
  readonly condition: string;      // 条件式の文字列表現
  readonly evaluatedTo: boolean;
  readonly branchTaken: 'then' | 'else';
  /** 条件の各部分の評価値（複合条件の追跡） */
  readonly conditionDetails: readonly {
    readonly part: string;
    readonly value: string;
  }[];
}

export interface PerformCallEvent {
  readonly eventType: 'perform-call';
  readonly timestamp: number;
  readonly paragraphName: string;
  readonly callDepth: number;
}

export interface PerformReturnEvent {
  readonly eventType: 'perform-return';
  readonly timestamp: number;
  readonly paragraphName: string;
  readonly callDepth: number;
}

export interface LoopIterationEvent {
  readonly eventType: 'loop-iteration';
  readonly timestamp: number;
  readonly paragraphName: string;
  readonly loopVar: string;
  readonly currentValue: string;
  readonly iteration: number;
}

export interface DisplayEvent {
  readonly eventType: 'display';
  readonly timestamp: number;
  readonly outputText: string;
}

export interface ProgramStartEvent {
  readonly eventType: 'program-start';
  readonly timestamp: number;
  readonly programId: string;
  readonly dataItemCount: number;
}

export interface ProgramEndEvent {
  readonly eventType: 'program-end';
  readonly timestamp: number;
  readonly programId: string;
  readonly totalStatements: number;
}

export type TraceEvent =
  | VarInitEvent
  | VarAssignEvent
  | ArithmeticEvent
  | BranchEvent
  | PerformCallEvent
  | PerformReturnEvent
  | LoopIterationEvent
  | DisplayEvent
  | ProgramStartEvent
  | ProgramEndEvent;

// ============================================================
// トレース収集器
// ============================================================

export class ExecutionTracer {
  private events: TraceEvent[] = [];
  private startTime: number;
  private statementCount: number = 0;
  private callDepth: number = 0;

  constructor() {
    this.startTime = Date.now();
  }

  private now(): number {
    return Date.now() - this.startTime;
  }

  incrementStatementCount(): void {
    this.statementCount++;
  }

  getStatementCount(): number {
    return this.statementCount;
  }

  getCallDepth(): number {
    return this.callDepth;
  }

  // --- イベント記録メソッド ---

  recordProgramStart(programId: string, dataItemCount: number): void {
    this.events.push({
      eventType: 'program-start',
      timestamp: this.now(),
      programId,
      dataItemCount,
    });
  }

  recordProgramEnd(programId: string): void {
    this.events.push({
      eventType: 'program-end',
      timestamp: this.now(),
      programId,
      totalStatements: this.statementCount,
    });
  }

  recordVarInit(varName: string, picClause: string, value: CobolValue): void {
    this.events.push({
      eventType: 'var-init',
      timestamp: this.now(),
      varName,
      picClause,
      initialValue: formatCobolValue(value),
      cobolType: value.kind,
    });
  }

  recordVarAssign(
    varName: string,
    previous: CobolValue,
    newVal: CobolValue,
    sourceInfo?: { sourceExpr: string; sourceType: string; conversionApplied: string }
  ): void {
    this.events.push({
      eventType: 'var-assign',
      timestamp: this.now(),
      varName,
      previousValue: formatCobolValue(previous),
      newValue: formatCobolValue(newVal),
      previousType: previous.kind,
      newType: newVal.kind,
      sourceInfo,
    });
  }

  recordArithmetic(
    operation: string,
    operands: { name: string; value: string }[],
    result: string,
    targetVar: string,
    rounded: boolean,
    roundingDetail?: { rawResult: string; roundedResult: string; truncatedDigits: number }
  ): void {
    this.events.push({
      eventType: 'arithmetic',
      timestamp: this.now(),
      operation,
      operands,
      result,
      targetVar,
      rounded,
      roundingDetail,
    });
  }

  recordBranch(
    condition: string,
    evaluatedTo: boolean,
    branchTaken: 'then' | 'else',
    conditionDetails: { part: string; value: string }[]
  ): void {
    this.events.push({
      eventType: 'branch',
      timestamp: this.now(),
      condition,
      evaluatedTo,
      branchTaken,
      conditionDetails,
    });
  }

  recordPerformCall(paragraphName: string): void {
    this.callDepth++;
    this.events.push({
      eventType: 'perform-call',
      timestamp: this.now(),
      paragraphName,
      callDepth: this.callDepth,
    });
  }

  recordPerformReturn(paragraphName: string): void {
    this.events.push({
      eventType: 'perform-return',
      timestamp: this.now(),
      paragraphName,
      callDepth: this.callDepth,
    });
    this.callDepth--;
  }

  recordLoopIteration(paragraphName: string, loopVar: string, currentValue: string, iteration: number): void {
    this.events.push({
      eventType: 'loop-iteration',
      timestamp: this.now(),
      paragraphName,
      loopVar,
      currentValue,
      iteration,
    });
  }

  recordDisplay(outputText: string): void {
    this.events.push({
      eventType: 'display',
      timestamp: this.now(),
      outputText,
    });
  }

  // --- トレース取得 ---

  getEvents(): readonly TraceEvent[] {
    return this.events;
  }

  /** トレースをJSON形式で出力 */
  toJSON(): string {
    return JSON.stringify(this.events, null, 2);
  }

  /** トレースのサマリーを生成 */
  getSummary(): TraceSummary {
    const varInits = this.events.filter(e => e.eventType === 'var-init') as VarInitEvent[];
    const assignments = this.events.filter(e => e.eventType === 'var-assign') as VarAssignEvent[];
    const arithmetics = this.events.filter(e => e.eventType === 'arithmetic') as ArithmeticEvent[];
    const branches = this.events.filter(e => e.eventType === 'branch') as BranchEvent[];
    const performCalls = this.events.filter(e => e.eventType === 'perform-call') as PerformCallEvent[];
    const loops = this.events.filter(e => e.eventType === 'loop-iteration') as LoopIterationEvent[];

    // 変数の型遷移マップ
    const typeTransitions = new Map<string, string[]>();
    for (const a of assignments) {
      if (a.sourceInfo?.conversionApplied && a.sourceInfo.conversionApplied !== 'none') {
        const key = `${a.varName}`;
        const existing = typeTransitions.get(key) || [];
        existing.push(`${a.sourceInfo.sourceType} → ${a.newType} (${a.sourceInfo.conversionApplied})`);
        typeTransitions.set(key, existing);
      }
    }

    // 分岐カバレッジ
    const branchCoverage = new Map<string, { then: number; else: number }>();
    for (const b of branches) {
      const key = b.condition;
      const existing = branchCoverage.get(key) || { then: 0, else: 0 };
      existing[b.branchTaken]++;
      branchCoverage.set(key, existing);
    }

    // パラグラフ呼び出し回数
    const paragraphCalls = new Map<string, number>();
    for (const p of performCalls) {
      paragraphCalls.set(p.paragraphName, (paragraphCalls.get(p.paragraphName) || 0) + 1);
    }

    return {
      totalEvents: this.events.length,
      totalStatements: this.statementCount,
      variableCount: varInits.length,
      assignmentCount: assignments.length,
      arithmeticCount: arithmetics.length,
      branchCount: branches.length,
      performCallCount: performCalls.length,
      loopIterationCount: loops.length,
      typeTransitions: Object.fromEntries(typeTransitions),
      branchCoverage: Object.fromEntries(branchCoverage),
      paragraphCalls: Object.fromEntries(paragraphCalls),
      roundingOperations: arithmetics.filter(a => a.roundingDetail).length,
    };
  }
}

export interface TraceSummary {
  totalEvents: number;
  totalStatements: number;
  variableCount: number;
  assignmentCount: number;
  arithmeticCount: number;
  branchCount: number;
  performCallCount: number;
  loopIterationCount: number;
  typeTransitions: Record<string, string[]>;
  branchCoverage: Record<string, { then: number; else: number }>;
  paragraphCalls: Record<string, number>;
  roundingOperations: number;
}
