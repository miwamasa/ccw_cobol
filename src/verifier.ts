/**
 * Property Verifier - 実行トレースに対するプロパティ検証エンジン
 *
 * 実行トレースを走査し、各プロパティが成立するかどうかを検証する。
 * 検証結果は PropertyVerificationResult として返される。
 *
 * 検証アプローチ:
 * - DataInvariant:    変数代入イベントごとに条件をチェック
 * - Precondition:     perform-call イベント時に条件をチェック
 * - Postcondition:    perform-return イベント時に条件をチェック
 * - Relational:       指定パラグラフの return 後にチェック
 * - Precision:        arithmetic イベントの丸め詳細を検査
 * - OutputEquivalence: display イベントを収集し比較用に保存
 * - LoopBound:        loop-iteration イベントのカウントを検査
 * - FinalState:       program-end 時点の変数値を検査
 */

import {
  Property, PropertySet, PropertyCondition, PropertyExpression,
  DataInvariant, Precondition, Postcondition, RelationalProperty,
  PrecisionProperty, OutputEquivalence, LoopBound, FinalStateProperty,
} from './properties';
import {
  TraceEvent, VarAssignEvent, VarInitEvent, ArithmeticEvent,
  PerformCallEvent, PerformReturnEvent, LoopIterationEvent, DisplayEvent,
} from './tracer';
import { CobolValue, decimalToNumber } from './types';

// ============================================================
// 検証結果の型
// ============================================================

export type VerificationStatus = 'passed' | 'failed' | 'skipped';

export interface PropertyVerificationResult {
  readonly propertyId: string;
  readonly propertyType: Property['propertyType'];
  readonly description: string;
  readonly status: VerificationStatus;
  /** 検証の詳細メッセージ */
  readonly message: string;
  /** 失敗時: 違反が発生した箇所 */
  readonly violations: readonly Violation[];
  /** 検証に使われたトレースイベント数 */
  readonly eventsChecked: number;
}

export interface Violation {
  readonly eventIndex: number;
  readonly eventType: string;
  readonly detail: string;
  /** 違反時の実際の値 */
  readonly actualValues: Record<string, string>;
}

export interface VerificationReport {
  readonly programId: string;
  readonly propertySetVersion: string;
  readonly timestamp: string;
  readonly results: readonly PropertyVerificationResult[];
  readonly summary: {
    readonly total: number;
    readonly passed: number;
    readonly failed: number;
    readonly skipped: number;
  };
  /** 全プロパティが成立したか */
  readonly allPassed: boolean;
}

// ============================================================
// 変数状態の追跡（トレースから再構築）
// ============================================================

interface VarState {
  name: string;
  numericValue: number;
  stringValue: string;
  kind: string;
}

class VariableStateTracker {
  private state: Map<string, VarState> = new Map();

  applyInit(event: VarInitEvent): void {
    const numVal = parseFloat(event.initialValue) || 0;
    this.state.set(event.varName, {
      name: event.varName,
      numericValue: numVal,
      stringValue: event.initialValue,
      kind: event.cobolType,
    });
  }

  applyAssign(event: VarAssignEvent): void {
    const numVal = parseFloat(event.newValue) || 0;
    this.state.set(event.varName, {
      name: event.varName,
      numericValue: numVal,
      stringValue: event.newValue,
      kind: event.newType,
    });
  }

  getNumericValue(varName: string): number {
    const s = this.state.get(varName);
    return s ? s.numericValue : 0;
  }

  getStringValue(varName: string): string {
    const s = this.state.get(varName);
    return s ? s.stringValue : '';
  }

  getSnapshot(): Map<string, VarState> {
    return new Map(this.state);
  }
}

// ============================================================
// メイン検証エンジン
// ============================================================

export class PropertyVerifier {
  private events: readonly TraceEvent[];
  private finalVariables: Map<string, CobolValue>;
  private displayOutput: string[];

  constructor(
    events: readonly TraceEvent[],
    finalVariables: Map<string, CobolValue>,
    displayOutput: string[]
  ) {
    this.events = events;
    this.finalVariables = finalVariables;
    this.displayOutput = displayOutput;
  }

  /**
   * PropertySetの全プロパティを検証し、レポートを生成する
   */
  verify(propertySet: PropertySet): VerificationReport {
    const results: PropertyVerificationResult[] = [];

    for (const prop of propertySet.properties) {
      results.push(this.verifyProperty(prop));
    }

    const passed = results.filter(r => r.status === 'passed').length;
    const failed = results.filter(r => r.status === 'failed').length;
    const skipped = results.filter(r => r.status === 'skipped').length;

    return {
      programId: propertySet.programId,
      propertySetVersion: propertySet.version,
      timestamp: new Date().toISOString(),
      results,
      summary: { total: results.length, passed, failed, skipped },
      allPassed: failed === 0,
    };
  }

  private verifyProperty(prop: Property): PropertyVerificationResult {
    switch (prop.propertyType) {
      case 'data-invariant':    return this.verifyDataInvariant(prop);
      case 'precondition':      return this.verifyPrecondition(prop);
      case 'postcondition':     return this.verifyPostcondition(prop);
      case 'relational':        return this.verifyRelational(prop);
      case 'precision':         return this.verifyPrecision(prop);
      case 'output-equivalence': return this.verifyOutputEquivalence(prop);
      case 'loop-bound':        return this.verifyLoopBound(prop);
      case 'final-state':       return this.verifyFinalState(prop);
    }
  }

  // ============================================================
  // DataInvariant の検証
  // ============================================================

  private verifyDataInvariant(prop: DataInvariant): PropertyVerificationResult {
    const tracker = new VariableStateTracker();
    const violations: Violation[] = [];
    let eventsChecked = 0;

    for (let i = 0; i < this.events.length; i++) {
      const event = this.events[i];

      // 状態を更新
      if (event.eventType === 'var-init') {
        tracker.applyInit(event);
      } else if (event.eventType === 'var-assign') {
        tracker.applyAssign(event);
      }

      // 指定タイミングで検証
      let shouldCheck = false;
      if (prop.checkAt === 'every-assignment') {
        shouldCheck = (event.eventType === 'var-assign' && event.varName === prop.targetVar);
      } else if (prop.checkAt === 'after-paragraph') {
        shouldCheck = (event.eventType === 'perform-return');
      } else if (prop.checkAt === 'at-end') {
        shouldCheck = (event.eventType === 'program-end');
      }

      if (shouldCheck) {
        eventsChecked++;
        if (!this.evaluateCondition(prop.condition, tracker)) {
          violations.push({
            eventIndex: i,
            eventType: event.eventType,
            detail: `Invariant violated: ${prop.description}`,
            actualValues: { [prop.targetVar]: tracker.getStringValue(prop.targetVar) },
          });
        }
      }
    }

    return {
      propertyId: prop.id,
      propertyType: prop.propertyType,
      description: prop.description,
      status: violations.length === 0 ? 'passed' : 'failed',
      message: violations.length === 0
        ? `Invariant held across ${eventsChecked} check points`
        : `Invariant violated ${violations.length} time(s)`,
      violations,
      eventsChecked,
    };
  }

  // ============================================================
  // Precondition の検証
  // ============================================================

  private verifyPrecondition(prop: Precondition): PropertyVerificationResult {
    const tracker = new VariableStateTracker();
    const violations: Violation[] = [];
    let eventsChecked = 0;

    for (let i = 0; i < this.events.length; i++) {
      const event = this.events[i];

      if (event.eventType === 'var-init') tracker.applyInit(event);
      else if (event.eventType === 'var-assign') tracker.applyAssign(event);

      if (event.eventType === 'perform-call' && event.paragraphName === prop.paragraphName) {
        eventsChecked++;
        if (!this.evaluateCondition(prop.condition, tracker)) {
          const snapshot = tracker.getSnapshot();
          const actualValues: Record<string, string> = {};
          for (const [k, v] of snapshot) actualValues[k] = v.stringValue;
          violations.push({
            eventIndex: i,
            eventType: event.eventType,
            detail: `Precondition not met before "${prop.paragraphName}"`,
            actualValues,
          });
        }
      }
    }

    if (eventsChecked === 0) {
      return {
        propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
        status: 'skipped', message: `Paragraph "${prop.paragraphName}" was never called`,
        violations: [], eventsChecked: 0,
      };
    }

    return {
      propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
      status: violations.length === 0 ? 'passed' : 'failed',
      message: violations.length === 0
        ? `Precondition held for ${eventsChecked} call(s) to "${prop.paragraphName}"`
        : `Precondition violated ${violations.length} time(s)`,
      violations, eventsChecked,
    };
  }

  // ============================================================
  // Postcondition の検証
  // ============================================================

  private verifyPostcondition(prop: Postcondition): PropertyVerificationResult {
    const tracker = new VariableStateTracker();
    const violations: Violation[] = [];
    let eventsChecked = 0;

    for (let i = 0; i < this.events.length; i++) {
      const event = this.events[i];

      if (event.eventType === 'var-init') tracker.applyInit(event);
      else if (event.eventType === 'var-assign') tracker.applyAssign(event);

      if (event.eventType === 'perform-return' && event.paragraphName === prop.paragraphName) {
        eventsChecked++;
        if (!this.evaluateCondition(prop.condition, tracker)) {
          const snapshot = tracker.getSnapshot();
          const actualValues: Record<string, string> = {};
          for (const [k, v] of snapshot) actualValues[k] = v.stringValue;
          violations.push({
            eventIndex: i,
            eventType: event.eventType,
            detail: `Postcondition not met after "${prop.paragraphName}"`,
            actualValues,
          });
        }
      }
    }

    if (eventsChecked === 0) {
      return {
        propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
        status: 'skipped', message: `Paragraph "${prop.paragraphName}" was never called`,
        violations: [], eventsChecked: 0,
      };
    }

    return {
      propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
      status: violations.length === 0 ? 'passed' : 'failed',
      message: violations.length === 0
        ? `Postcondition held for ${eventsChecked} return(s) from "${prop.paragraphName}"`
        : `Postcondition violated ${violations.length} time(s)`,
      violations, eventsChecked,
    };
  }

  // ============================================================
  // RelationalProperty の検証
  // ============================================================

  private verifyRelational(prop: RelationalProperty): PropertyVerificationResult {
    const tracker = new VariableStateTracker();
    const violations: Violation[] = [];
    let eventsChecked = 0;

    for (let i = 0; i < this.events.length; i++) {
      const event = this.events[i];

      if (event.eventType === 'var-init') tracker.applyInit(event);
      else if (event.eventType === 'var-assign') tracker.applyAssign(event);

      if (event.eventType === 'perform-return' && event.paragraphName === prop.checkAfterParagraph) {
        eventsChecked++;
        if (!this.evaluateConditionWithTolerance(prop.condition, tracker, prop.tolerance)) {
          const snapshot = tracker.getSnapshot();
          const actualValues: Record<string, string> = {};
          for (const [k, v] of snapshot) actualValues[k] = v.stringValue;
          violations.push({
            eventIndex: i,
            eventType: event.eventType,
            detail: `Relational property violated: ${prop.description}`,
            actualValues,
          });
        }
      }
    }

    if (eventsChecked === 0) {
      return {
        propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
        status: 'skipped', message: `Paragraph "${prop.checkAfterParagraph}" was never called`,
        violations: [], eventsChecked: 0,
      };
    }

    return {
      propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
      status: violations.length === 0 ? 'passed' : 'failed',
      message: violations.length === 0
        ? `Relational property held across ${eventsChecked} check(s)`
        : `Relational property violated ${violations.length} time(s)`,
      violations, eventsChecked,
    };
  }

  // ============================================================
  // PrecisionProperty の検証
  // ============================================================

  private verifyPrecision(prop: PrecisionProperty): PropertyVerificationResult {
    const arithmeticEvents = this.events.filter(
      e => e.eventType === 'arithmetic' && (e as ArithmeticEvent).targetVar === prop.targetVar
    ) as ArithmeticEvent[];

    if (arithmeticEvents.length === 0) {
      return {
        propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
        status: 'skipped', message: `No arithmetic operations found for "${prop.targetVar}"`,
        violations: [], eventsChecked: 0,
      };
    }

    const violations: Violation[] = [];

    for (let i = 0; i < arithmeticEvents.length; i++) {
      const ae = arithmeticEvents[i];

      // 丸めモードチェック
      if (prop.roundingMode === 'must-round' && !ae.rounded) {
        violations.push({
          eventIndex: this.events.indexOf(ae),
          eventType: ae.eventType,
          detail: `Expected ROUNDED but operation was not rounded`,
          actualValues: { result: ae.result, rounded: String(ae.rounded) },
        });
      }
      if (prop.roundingMode === 'must-truncate' && ae.rounded) {
        violations.push({
          eventIndex: this.events.indexOf(ae),
          eventType: ae.eventType,
          detail: `Expected TRUNCATION but operation was ROUNDED`,
          actualValues: { result: ae.result, rounded: String(ae.rounded) },
        });
      }

      // 精度チェック: 結果値の小数桁数が要求を満たしているか
      const resultStr = ae.result;
      const dotIndex = resultStr.indexOf('.');
      if (dotIndex >= 0) {
        const actualDecimals = resultStr.length - dotIndex - 1;
        if (actualDecimals < prop.minDecimalPlaces) {
          violations.push({
            eventIndex: this.events.indexOf(ae),
            eventType: ae.eventType,
            detail: `Precision insufficient: ${actualDecimals} decimal places < required ${prop.minDecimalPlaces}`,
            actualValues: { result: ae.result, actualDecimals: String(actualDecimals) },
          });
        }
      }
    }

    return {
      propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
      status: violations.length === 0 ? 'passed' : 'failed',
      message: violations.length === 0
        ? `Precision property held across ${arithmeticEvents.length} arithmetic operation(s)`
        : `Precision property violated ${violations.length} time(s)`,
      violations, eventsChecked: arithmeticEvents.length,
    };
  }

  // ============================================================
  // OutputEquivalence の検証（ソース側の出力収集）
  // ============================================================

  private verifyOutputEquivalence(prop: OutputEquivalence): PropertyVerificationResult {
    // この検証は単体では「収集」フェーズ。
    // 実際の比較は CrossVerifier で行う。
    // ここでは出力が存在することを確認する。
    const displayEvents = this.events.filter(e => e.eventType === 'display') as DisplayEvent[];

    if (displayEvents.length === 0) {
      return {
        propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
        status: 'skipped', message: 'No DISPLAY output found',
        violations: [], eventsChecked: 0,
      };
    }

    const relevantOutputs = prop.lineIndices
      ? prop.lineIndices.map(i => this.displayOutput[i]).filter(Boolean)
      : this.displayOutput;

    return {
      propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
      status: 'passed',
      message: `Collected ${relevantOutputs.length} output line(s) for cross-verification`,
      violations: [], eventsChecked: displayEvents.length,
    };
  }

  // ============================================================
  // LoopBound の検証
  // ============================================================

  private verifyLoopBound(prop: LoopBound): PropertyVerificationResult {
    const loopEvents = this.events.filter(
      e => e.eventType === 'loop-iteration' && (e as LoopIterationEvent).paragraphName === prop.paragraphName
    ) as LoopIterationEvent[];

    if (loopEvents.length === 0) {
      return {
        propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
        status: 'skipped', message: `No loop iterations found for "${prop.paragraphName}"`,
        violations: [], eventsChecked: 0,
      };
    }

    const maxIteration = Math.max(...loopEvents.map(e => e.iteration));
    const violations: Violation[] = [];

    if (maxIteration > prop.maxIterations) {
      violations.push({
        eventIndex: this.events.indexOf(loopEvents[loopEvents.length - 1]),
        eventType: 'loop-iteration',
        detail: `Loop exceeded bound: ${maxIteration} > ${prop.maxIterations}`,
        actualValues: { maxIteration: String(maxIteration), bound: String(prop.maxIterations) },
      });
    }

    return {
      propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
      status: violations.length === 0 ? 'passed' : 'failed',
      message: violations.length === 0
        ? `Loop bounded: ${maxIteration} iterations <= ${prop.maxIterations}`
        : `Loop exceeded bound: ${maxIteration} > ${prop.maxIterations}`,
      violations, eventsChecked: loopEvents.length,
    };
  }

  // ============================================================
  // FinalState の検証
  // ============================================================

  private verifyFinalState(prop: FinalStateProperty): PropertyVerificationResult {
    const finalVal = this.finalVariables.get(prop.targetVar);
    if (!finalVal) {
      return {
        propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
        status: 'failed', message: `Variable "${prop.targetVar}" not found in final state`,
        violations: [{ eventIndex: -1, eventType: 'final', detail: 'Variable not found', actualValues: {} }],
        eventsChecked: 0,
      };
    }

    const violations: Violation[] = [];

    if (typeof prop.expectedValue === 'number') {
      // 数値比較
      const actualNum = finalVal.kind === 'fixed-decimal' ? decimalToNumber(finalVal) : 0;
      const tolerance = prop.tolerance ?? 0;
      if (Math.abs(actualNum - prop.expectedValue) > tolerance) {
        violations.push({
          eventIndex: -1,
          eventType: 'final-state',
          detail: `Expected ${prop.expectedValue} (+-${tolerance}), got ${actualNum}`,
          actualValues: { [prop.targetVar]: String(actualNum) },
        });
      }
    } else {
      // 文字列比較
      const actualStr = finalVal.kind === 'alphanumeric' ? finalVal.bytes.trimEnd() : '';
      if (actualStr !== prop.expectedValue) {
        violations.push({
          eventIndex: -1,
          eventType: 'final-state',
          detail: `Expected "${prop.expectedValue}", got "${actualStr}"`,
          actualValues: { [prop.targetVar]: actualStr },
        });
      }
    }

    return {
      propertyId: prop.id, propertyType: prop.propertyType, description: prop.description,
      status: violations.length === 0 ? 'passed' : 'failed',
      message: violations.length === 0
        ? `Final state matches expected value`
        : `Final state mismatch`,
      violations, eventsChecked: 1,
    };
  }

  // ============================================================
  // 条件評価ヘルパー
  // ============================================================

  private evaluateCondition(cond: PropertyCondition, tracker: VariableStateTracker): boolean {
    return this.evaluateConditionWithTolerance(cond, tracker, 0);
  }

  private evaluateConditionWithTolerance(
    cond: PropertyCondition, tracker: VariableStateTracker, tolerance: number
  ): boolean {
    if ('logicalOp' in cond) {
      if (cond.logicalOp === 'AND') {
        return cond.conditions.every(c => this.evaluateConditionWithTolerance(c, tracker, tolerance));
      } else {
        return cond.conditions.some(c => this.evaluateConditionWithTolerance(c, tracker, tolerance));
      }
    }

    // PropertyComparison
    const left = this.evaluateExpression(cond.left, tracker);
    const right = this.evaluateExpression(cond.right, tracker);

    switch (cond.op) {
      case '=':  return Math.abs(left - right) <= tolerance;
      case '!=': return Math.abs(left - right) > tolerance;
      case '>':  return left > right - tolerance;
      case '<':  return left < right + tolerance;
      case '>=': return left >= right - tolerance;
      case '<=': return left <= right + tolerance;
    }
  }

  private evaluateExpression(expr: PropertyExpression, tracker: VariableStateTracker): number {
    switch (expr.kind) {
      case 'var-ref':
        return tracker.getNumericValue(expr.varName);
      case 'literal':
        return typeof expr.value === 'number' ? expr.value : parseFloat(expr.value) || 0;
      case 'binary-op': {
        const l = this.evaluateExpression(expr.left, tracker);
        const r = this.evaluateExpression(expr.right, tracker);
        switch (expr.op) {
          case '+': return l + r;
          case '-': return l - r;
          case '*': return l * r;
          case '/': return r !== 0 ? l / r : 0;
        }
      }
      case 'abs':
        return Math.abs(this.evaluateExpression(expr.operand, tracker));
    }
  }
}
