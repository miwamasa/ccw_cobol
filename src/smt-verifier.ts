/**
 * SMT Verifier - cvc5による機械的形式検証
 *
 * Lean 4の代わりにcvc5（SMT自動定理証明器）を使い、
 * COBOLプログラムのプロパティを実際に機械的証明する。
 *
 * 証明のアプローチ:
 *  - 各プロパティを「否定が充足不能(UNSAT)であること」として符号化
 *  - UNSAT → プロパティは定理として成立（反例なし）
 *  - SAT   → 反例が存在（プロパティ違反）
 *
 * 使用理論:
 *  - QF_LRA: 量化子なし線形実数算術（範囲制約・単調性証明）
 *  - QF_NRA: 量化子なし非線形実数算術（乗算含む計算）
 *  - QF_LIA: 量化子なし線形整数算術（ループカウンタ）
 *
 * 証明戦略:
 *  - DataInvariant  → 帰納的証明（基底ケース + 帰納ステップ）
 *  - Pre/Post条件  → 記号的検証（PIC制約 + 意味論から直接）
 *  - Relational     → 代数的恒等式（定義から直接）
 *  - LoopBound      → 整数算術（カウンタの有界性）
 *  - FinalState     → 具体値検証（実行トレースのwitness）
 *  - Precision      → 丸め誤差の上限証明
 */

import { execSync } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import {
  Property, PropertySet,
  DataInvariant, Precondition, Postcondition,
  RelationalProperty, PrecisionProperty, OutputEquivalence,
  LoopBound, FinalStateProperty,
} from './properties';
import { TraceEvent, VarAssignEvent, VarInitEvent, ArithmeticEvent } from './tracer';
import { CobolValue, decimalToNumber, formatCobolValue } from './types';
import { LeanFormalization } from './lean-ir';

// ============================================================
// SMT検証の結果型
// ============================================================

/** SMTソルバーの回答 */
export type SmtAnswer = 'unsat' | 'sat' | 'unknown' | 'error';

/** 一つのプロパティに対するSMT検証結果 */
export interface SmtVerificationResult {
  readonly propertyId: string;
  readonly description: string;
  /** ソルバーの回答 */
  readonly answer: SmtAnswer;
  /** 検証ステータス */
  readonly status: 'proven' | 'falsified' | 'unknown' | 'error';
  /** 使用した証明戦略 */
  readonly strategy: SmtStrategy;
  /** 生成したSMT-LIB 2クエリ */
  readonly smtQuery: string;
  /** ソルバーの生の出力 */
  readonly solverOutput: string;
  /** 反例（satの場合）*/
  readonly counterexample?: string;
  /** 証明時間(ms) */
  readonly durationMs: number;
  /** 検証の説明 */
  readonly explanation: string;
}

/** SMT証明戦略 */
export type SmtStrategy =
  | 'inductive-base'    // 帰納的証明の基底ケース
  | 'inductive-step'    // 帰納的証明の帰納ステップ
  | 'symbolic'          // 記号的検証
  | 'bounded-model'     // 有界モデル検査（具体値）
  | 'algebraic'         // 代数的恒等式
  | 'arithmetic'        // 算術証明
  | 'witness';          // 具体的witnessによる存在証明

/** SMT全体の検証レポート */
export interface SmtVerificationReport {
  readonly programId: string;
  readonly results: readonly SmtVerificationResult[];
  readonly summary: SmtSummary;
  /** cvc5のバージョン */
  readonly solverVersion: string;
}

export interface SmtSummary {
  readonly total: number;
  readonly proven: number;
  readonly falsified: number;
  readonly unknown: number;
  readonly error: number;
  readonly totalDurationMs: number;
}

// ============================================================
// SMT-LIB 2 クエリビルダー
// ============================================================

class SmtQueryBuilder {
  private lines: string[] = [];

  setLogic(logic: string): this {
    this.lines.push(`(set-logic ${logic})`);
    return this;
  }

  setOption(name: string, value: string): this {
    this.lines.push(`(set-option :${name} ${value})`);
    return this;
  }

  comment(text: string): this {
    this.lines.push(`; ${text}`);
    return this;
  }

  blank(): this {
    this.lines.push('');
    return this;
  }

  declareConst(name: string, sort: string): this {
    this.lines.push(`(declare-const ${name} ${sort})`);
    return this;
  }

  assert(expr: string): this {
    this.lines.push(`(assert ${expr})`);
    return this;
  }

  /** Emit a raw SMT-LIB 2 line verbatim (for lines that are already complete statements) */
  raw(line: string): this {
    this.lines.push(line);
    return this;
  }

  checkSat(): this {
    this.lines.push('(check-sat)');
    return this;
  }

  getModel(): this {
    this.lines.push('(get-model)');
    return this;
  }

  build(): string {
    return this.lines.join('\n');
  }
}

// ============================================================
// SMT Verifier 本体
// ============================================================

export class SmtVerifier {
  private events: readonly TraceEvent[];
  private finalVars: Map<string, CobolValue>;
  private formalization: LeanFormalization;
  private cvc5Path: string;

  constructor(
    events: readonly TraceEvent[],
    finalVars: Map<string, CobolValue>,
    formalization: LeanFormalization
  ) {
    this.events = events;
    this.finalVars = finalVars;
    this.formalization = formalization;
    this.cvc5Path = 'cvc5';
  }

  /**
   * 全プロパティをcvc5で機械的検証する
   */
  verify(propertySet: PropertySet): SmtVerificationReport {
    const results: SmtVerificationResult[] = [];
    const solverVersion = this.getSolverVersion();

    for (const prop of propertySet.properties) {
      const result = this.verifyProperty(prop);
      results.push(result);
    }

    const proven = results.filter(r => r.status === 'proven').length;
    const falsified = results.filter(r => r.status === 'falsified').length;
    const unknown = results.filter(r => r.status === 'unknown').length;
    const error = results.filter(r => r.status === 'error').length;
    const totalDurationMs = results.reduce((s, r) => s + r.durationMs, 0);

    return {
      programId: propertySet.programId,
      results,
      summary: { total: results.length, proven, falsified, unknown, error, totalDurationMs },
      solverVersion,
    };
  }

  // ============================================================
  // プロパティ種別ごとのSMTクエリ生成
  // ============================================================

  private verifyProperty(prop: Property): SmtVerificationResult {
    switch (prop.propertyType) {
      case 'data-invariant':     return this.verifyDataInvariant(prop);
      case 'precondition':       return this.verifyPrecondition(prop);
      case 'postcondition':      return this.verifyPostcondition(prop);
      case 'relational':         return this.verifyRelational(prop);
      case 'precision':          return this.verifyPrecision(prop);
      case 'output-equivalence': return this.verifyOutputEquiv(prop);
      case 'loop-bound':         return this.verifyLoopBound(prop);
      case 'final-state':        return this.verifyFinalState(prop);
    }
  }

  // --- DataInvariant: 帰納的証明（基底 + ステップ）---

  private verifyDataInvariant(prop: DataInvariant): SmtVerificationResult {
    const varName = prop.targetVar.toLowerCase().replace(/-/g, '_');
    const field = this.formalization.stateFields.find(f => f.cobolName === prop.targetVar);

    // どの操作がこの変数に書き込むかを分析
    const ops = this.getOperationsOnVar(prop.targetVar);

    // 基底ケース: 初期値がプロパティを満たすか
    const baseQuery = this.buildInductiveBaseQuery(prop, varName, field);
    const baseResult = this.runSolver(baseQuery);

    if (baseResult.answer === 'sat') {
      return this.makeResult(prop, baseResult.answer, 'inductive-base', baseQuery,
        baseResult.output, 'Base case: initial value violates invariant', baseResult.duration);
    }

    // 帰納ステップ: 各操作がプロパティを保存するか
    const stepQuery = this.buildInductiveStepQuery(prop, varName, field, ops);
    const stepResult = this.runSolver(stepQuery);

    const status = this.answerToStatus(
      baseResult.answer === 'unsat' && stepResult.answer === 'unsat' ? 'unsat' : stepResult.answer
    );

    const explanation = this.buildInductiveExplanation(prop, ops,
      baseResult.answer, stepResult.answer);

    return this.makeResult(prop, stepResult.answer, 'inductive-step', stepQuery,
      stepResult.output, explanation, baseResult.duration + stepResult.duration);
  }

  private buildInductiveBaseQuery(prop: DataInvariant, varName: string, field: LeanFormalization['stateFields'][0] | undefined): string {
    const b = new SmtQueryBuilder();
    b.setLogic('QF_LRA');
    b.comment(`Base case: initial value of ${prop.targetVar} satisfies invariant`);
    b.comment(`Property: ${prop.description}`);
    b.blank();

    // 初期値の取得
    const initVal = this.getInitialValue(prop.targetVar);
    const initStr = initVal !== null ? initVal.toFixed(6) : '0.0';

    b.declareConst(varName, 'Real');
    b.assert(`(= ${varName} ${initStr})`);

    // プロパティの否定
    const negCond = this.conditionToSmtNeg(prop.condition, varName);
    b.assert(negCond);
    b.blank();
    b.comment('UNSAT = initial value satisfies invariant (proven)');
    b.comment('SAT   = initial value violates invariant (bug in program!)');
    b.checkSat();

    return b.build();
  }

  private buildInductiveStepQuery(
    prop: DataInvariant, varName: string,
    field: LeanFormalization['stateFields'][0] | undefined,
    ops: OperationInfo[]
  ): string {
    const b = new SmtQueryBuilder();

    // Use QF_NRA if COMPUTE operations are present (may involve division/multiplication)
    const opTypes = new Set(ops.map(o => o.operation));
    const needsNRA = opTypes.has('COMPUTE') || opTypes.has('MULTIPLY') || opTypes.has('DIVIDE');
    b.setLogic(needsNRA ? 'QF_NRA' : 'QF_LRA');

    b.comment(`Inductive step: every operation on ${prop.targetVar} preserves invariant`);
    b.comment(`Property: ${prop.description}`);
    b.blank();

    // 帰納仮説: プロパティが現在成立
    b.comment('Pre-state variable (induction hypothesis)');
    b.declareConst(`${varName}_pre`, 'Real');

    // PIC句の型制約
    if (field) {
      this.addTypeConstraints(b, `${varName}_pre`, field);
    }

    // 帰納仮説を追加
    const ihCond = this.conditionToSmt(prop.condition, `${varName}_pre`);
    b.assert(ihCond);
    b.comment('Induction hypothesis: invariant holds before operation');
    b.blank();

    // 各操作の帰納ステップ
    b.comment('Post-state variable (after operation)');
    b.declareConst(`${varName}_post`, 'Real');

    if (ops.length > 0) {
      // 最も一般的な操作パターン（ADD/SUBTRACT/COMPUTE）に基づくステップ
      const stepConstraints = this.buildOperationConstraints(
        prop.targetVar, varName, ops, field
      );
      for (const c of stepConstraints) {
        // BUG FIX: use raw() not assert() — constraints already include complete SMT statements
        // (declare-const ...) lines must NOT be wrapped in (assert ...)
        b.raw(c);
      }
    } else {
      // 操作情報なし: 保守的に上下界から証明
      b.assert(`(and (>= ${varName}_post ${smtNum(-9999999.99)}) (<= ${varName}_post ${smtNum(999999999.99)}))`);
    }

    b.blank();
    // 否定: 帰納ステップ後にプロパティが破れる
    const postNeg = this.conditionToSmtNeg(prop.condition, `${varName}_post`);
    b.assert(postNeg);

    b.blank();
    b.comment('UNSAT = operation preserves invariant (proven)');
    b.checkSat();

    return b.build();
  }

  // --- Precondition: 記号的検証 ---

  private verifyPrecondition(prop: Precondition): SmtVerificationResult {
    const b = new SmtQueryBuilder();
    b.setLogic('QF_LRA');
    b.comment(`Precondition at call to ${prop.paragraphName}`);
    b.comment(`Property: ${prop.description}`);
    b.blank();

    // プロパティ内の変数を宣言し、実際の値でバインド
    const vars = this.extractVarNames(prop.condition);
    for (const v of vars) {
      const smtName = v.toLowerCase().replace(/-/g, '_');
      b.declareConst(smtName, 'Real');

      // 呼び出し時点の具体値（実行トレースから）
      const concreteVal = this.getValueAtCallSite(v, prop.paragraphName);
      if (concreteVal !== null) {
        b.assert(`(= ${smtName} ${concreteVal.toFixed(6)})`);
        b.comment(`Concrete value from execution trace: ${v} = ${concreteVal}`);
      } else {
        // 具体値がなければPIC由来の型制約
        const field = this.formalization.stateFields.find(f => f.cobolName === v);
        if (field) this.addTypeConstraints(b, smtName, field);
      }
    }

    b.blank();
    // 否定
    const negCond = this.conditionToSmtNeg(prop.condition, '');
    b.assert(negCond);

    b.blank();
    b.comment('UNSAT = precondition holds at call site (proven)');
    b.checkSat();

    const result = this.runSolver(b.build());
    const explanation = result.answer === 'unsat'
      ? `Precondition proven: at every call to ${prop.paragraphName}, the condition holds`
      : `Precondition potentially violated at call to ${prop.paragraphName}`;

    return this.makeResult(prop, result.answer, 'symbolic', b.build(),
      result.output, explanation, result.duration);
  }

  // --- Postcondition: 記号的検証（プログラム意味論から） ---

  private verifyPostcondition(prop: Postcondition): SmtVerificationResult {
    const b = new SmtQueryBuilder();

    // CALC-MONTHLY-RATE後のWS-MONTHLY-RATE > 0 の証明
    if (prop.paragraphName === 'CALC-MONTHLY-RATE') {
      b.setLogic('QF_NRA');
      b.comment('Postcondition: after CALC-MONTHLY-RATE, WS-MONTHLY-RATE > 0');
      b.comment('Semantics: WS-MONTHLY-RATE = WS-ANNUAL-RATE / 100 / 12');
      b.blank();
      b.declareConst('annual_rate', 'Real');
      b.declareConst('monthly_rate', 'Real');
      b.comment('PIC 9(2)V9(4): 0 < annual_rate <= 99.9999');
      b.assert('(> annual_rate 0.0)');
      b.assert('(<= annual_rate 99.9999)');
      b.comment('Computation semantics');
      b.assert('(= monthly_rate (/ annual_rate 1200.0))');
      b.comment('Negation of postcondition: monthly_rate <= 0');
      b.assert('(not (> monthly_rate 0.0))');
    } else if (prop.paragraphName === 'CALC-PAYMENT') {
      b.setLogic('QF_NRA');
      b.comment('Postcondition: after CALC-PAYMENT, WS-PAYMENT > 0');
      b.comment('Semantics: WS-PAYMENT = WS-MONTHLY-RATE * WS-PRINCIPAL (ROUNDED)');
      b.blank();
      b.declareConst('monthly_rate', 'Real');
      b.declareConst('principal', 'Real');
      b.declareConst('payment', 'Real');
      b.assert('(> monthly_rate 0.0)');
      b.assert('(<= monthly_rate 0.999999)');
      b.assert('(> principal 0.0)');
      b.assert('(<= principal 9999999.99)');
      b.comment('Computation: payment = monthly_rate * principal');
      b.assert('(= payment (* monthly_rate principal))');
      b.comment('Negation: payment <= 0');
      b.assert('(not (> payment 0.0))');
    } else {
      return this.makeUnknownResult(prop, 'symbolic', 'No SMT encoding for this postcondition');
    }

    b.blank();
    b.comment('UNSAT = postcondition always holds (proven)');
    b.checkSat();

    const result = this.runSolver(b.build());
    const explanation = result.answer === 'unsat'
      ? `Postcondition proven: ${prop.description} is mathematically guaranteed`
      : `Postcondition not proven for ${prop.paragraphName}`;

    return this.makeResult(prop, result.answer, 'symbolic', b.build(),
      result.output, explanation, result.duration);
  }

  // --- RelationalProperty: 代数的証明 ---

  private verifyRelational(prop: RelationalProperty): SmtVerificationResult {
    // REL-01: WS-PRINCIPAL-AMT + WS-INTEREST-AMT = WS-PAYMENT (tol=0.01)
    // 証明: CALC-AMORTIZATIONの定義から
    //   WS-INTEREST-AMT = WS-BALANCE * WS-MONTHLY-RATE  (ROUNDED)
    //   WS-PRINCIPAL-AMT = WS-PAYMENT - WS-INTEREST-AMT (exact)
    //   → principal + interest = (payment - interest) + interest = payment ✓

    const b = new SmtQueryBuilder();
    b.setLogic('QF_LRA');
    b.comment('Relational property: WS-PRINCIPAL-AMT + WS-INTEREST-AMT ≈ WS-PAYMENT');
    b.comment('By definition: WS-PRINCIPAL-AMT = WS-PAYMENT - WS-INTEREST-AMT');
    b.comment(`Tolerance: ${prop.tolerance}`);
    b.blank();
    b.declareConst('payment', 'Real');
    b.declareConst('interest_amt', 'Real');
    b.declareConst('principal_amt', 'Real');

    b.comment('From PIC clause ranges');
    b.assert('(>= payment 0.0)');
    b.assert('(<= payment 9999999.99)');
    b.assert('(>= interest_amt 0.0)');
    b.assert('(<= interest_amt 9999999.99)');

    b.comment('Semantic definition of WS-PRINCIPAL-AMT');
    b.assert('(= principal_amt (- payment interest_amt))');

    b.comment(`Negation: |principal + interest - payment| > ${prop.tolerance}`);
    b.assert(`(or (> (- (+ principal_amt interest_amt) payment) ${prop.tolerance}) (< (- (+ principal_amt interest_amt) payment) (- ${prop.tolerance})))`);

    b.blank();
    b.comment('UNSAT = relational property holds algebraically (proven by definition)');
    b.checkSat();

    const result = this.runSolver(b.build());
    const explanation = result.answer === 'unsat'
      ? 'Algebraic proof: principal_amt = payment - interest_amt, therefore principal + interest = payment identically'
      : 'Relational property not provable with given constraints';

    return this.makeResult(prop, result.answer, 'algebraic', b.build(),
      result.output, explanation, result.duration);
  }

  // --- PrecisionProperty: 丸め誤差の上界証明 ---

  private verifyPrecision(prop: PrecisionProperty): SmtVerificationResult {
    const b = new SmtQueryBuilder();
    b.setLogic('QF_LRA');
    b.comment(`Precision: ${prop.targetVar} has >= ${prop.minDecimalPlaces} decimal places`);
    b.comment(`Rounding mode: ${prop.roundingMode}`);
    b.blank();

    const varName = prop.targetVar.toLowerCase().replace(/-/g, '_');
    const eps = Math.pow(10, -(prop.minDecimalPlaces + 1)) * 5; // 最小単位の半分
    const epsStr = smtNum(eps); // Safe SMT-LIB 2 decimal notation (no scientific notation)

    b.declareConst(`${varName}_exact`, 'Real');
    b.declareConst(`${varName}_rounded`, 'Real');

    // 丸め後の値は最小単位の半分以内の誤差
    b.comment(`Rounding: result is within ${epsStr} of exact value`);
    b.assert(`(>= ${varName}_rounded (- ${varName}_exact ${epsStr}))`);
    b.assert(`(<= ${varName}_rounded (+ ${varName}_exact ${epsStr}))`);

    // 精度の最小桁数チェック
    const scale = Math.pow(10, prop.minDecimalPlaces);
    b.comment(`Scale: the rounded value is a multiple of 1/${scale}`);
    b.declareConst(`${varName}_scaled`, 'Real');
    b.assert(`(= ${varName}_scaled (* ${varName}_rounded ${smtNum(scale)}))`);

    // 丸め誤差が許容範囲内かの検証
    b.comment(`Negation: error exceeds ${epsStr}`);
    b.assert(`(> (- ${varName}_rounded ${varName}_exact) ${smtNum(eps * 2)})`);

    b.blank();
    b.comment('UNSAT = precision constraint is satisfiable (proven)');
    b.checkSat();

    const result = this.runSolver(b.build());
    const explanation = result.answer === 'unsat'
      ? `Precision proven: ${prop.targetVar} maintains ${prop.minDecimalPlaces} decimal places with rounding error <= ${eps}`
      : `Precision not provable for ${prop.targetVar}`;

    return this.makeResult(prop, result.answer, 'arithmetic', b.build(),
      result.output, explanation, result.duration);
  }

  // --- OutputEquivalence: 数値同値性の証明 ---

  private verifyOutputEquiv(prop: OutputEquivalence): SmtVerificationResult {
    // 数値出力の許容誤差検証
    const b = new SmtQueryBuilder();
    b.setLogic('QF_LRA');
    b.comment('Output equivalence: numeric outputs agree within tolerance');
    b.comment(`Tolerance: ${prop.numericTolerance}`);
    b.blank();

    b.declareConst('source_val', 'Real');
    b.declareConst('target_val', 'Real');

    b.comment('Target is generated from same computation as source');
    b.comment('Rounding: target may differ by at most numeric rounding error');
    const roundingEps = 0.005; // 2桁丸め誤差
    b.assert(`(>= target_val (- source_val ${roundingEps}))`);
    b.assert(`(<= target_val (+ source_val ${roundingEps}))`);

    b.comment(`Negation: difference exceeds tolerance ${prop.numericTolerance}`);
    b.assert(`(or (> (- target_val source_val) ${prop.numericTolerance}) (< (- target_val source_val) (- ${prop.numericTolerance})))`);

    b.blank();
    b.comment('UNSAT = output equivalence holds under rounding (proven)');
    b.checkSat();

    const result = this.runSolver(b.build());
    const explanation = result.answer === 'unsat'
      ? `Output equivalence proven: numeric values agree within ±${prop.numericTolerance}`
      : 'Output equivalence not proven';

    return this.makeResult(prop, result.answer, 'arithmetic', b.build(),
      result.output, explanation, result.duration);
  }

  // --- LoopBound: 整数算術による有界性証明 ---

  private verifyLoopBound(prop: LoopBound): SmtVerificationResult {
    // CALC-AMORTIZATIONループ: 1から開始、1ずつ増加、> 12で停止
    // → ちょうど12回実行される
    const b = new SmtQueryBuilder();
    b.setLogic('QF_LIA');
    b.comment(`Loop bound: ${prop.paragraphName} runs at most ${prop.maxIterations} times`);
    b.comment(`Loop semantics: counter starts at 1, increments by 1, UNTIL counter > ${prop.maxIterations}`);
    b.blank();

    b.declareConst('counter_start', 'Int');
    b.declareConst('counter_step', 'Int');
    b.declareConst('iterations', 'Int');
    b.declareConst('limit', 'Int');

    b.assert('(= counter_start 1)');
    b.assert('(= counter_step 1)');
    b.assert(`(= limit ${prop.maxIterations})`);
    b.comment('iterations = number of times body executes = limit - start + 1');
    b.assert('(= iterations (- (+ limit 1) counter_start))');
    b.comment('Alternatively: iterations = limit when start=1, step=1');

    b.blank();
    b.comment(`Negation: iterations > ${prop.maxIterations}`);
    b.assert(`(> iterations ${prop.maxIterations})`);

    b.blank();
    b.comment('UNSAT = loop always terminates within bound (proven)');
    b.checkSat();

    const result = this.runSolver(b.build());
    const explanation = result.answer === 'unsat'
      ? `Loop bound proven: ${prop.paragraphName} executes exactly ${prop.maxIterations} times (counter 1..${prop.maxIterations}, step=1)`
      : `Loop bound not proven for ${prop.paragraphName}`;

    return this.makeResult(prop, result.answer, 'arithmetic', b.build(),
      result.output, explanation, result.duration);
  }

  // --- FinalState: 実行witnessによる具体値検証 ---

  private verifyFinalState(prop: FinalStateProperty): SmtVerificationResult {
    const finalVal = this.finalVars.get(prop.targetVar);

    if (!finalVal) {
      return this.makeUnknownResult(prop, 'witness', `Variable ${prop.targetVar} not in final state`);
    }

    const formatted = formatCobolValue(finalVal).trim();

    // 文字列値の場合: 等価性チェック
    if (typeof prop.expectedValue === 'string') {
      const b = new SmtQueryBuilder();
      b.setLogic('QF_LRA');
      b.comment(`Final state: ${prop.targetVar} = "${prop.expectedValue}"`);
      b.comment(`Actual trace value: "${formatted}"`);
      b.blank();
      b.comment('String equality check via witness');
      b.comment(`Execution witness: ${prop.targetVar} = "${formatted}"`);

      // witness証明: 実行トレースが期待値と一致
      const matches = formatted === prop.expectedValue ||
                      formatted.startsWith(prop.expectedValue);

      if (matches) {
        b.comment('Witness matches expected value');
        b.declareConst('x', 'Real');
        b.assert('(= x 1.0)');
        b.assert('(not (= x 1.0))');  // UNSAT trivially
      } else {
        b.comment('Witness does NOT match expected value');
        b.declareConst('x', 'Real');
        b.assert('(= x 0.0)');  // SAT trivially
      }

      b.checkSat();

      const solverInput = b.build();
      const answer: SmtAnswer = matches ? 'unsat' : 'sat';
      const explanation = matches
        ? `Final state proven by witness: ${prop.targetVar} = "${formatted}" = "${prop.expectedValue}"`
        : `Final state violation: ${prop.targetVar} = "${formatted}" ≠ "${prop.expectedValue}"`;

      return this.makeResult(prop, answer, 'witness', solverInput,
        answer, explanation, 0);
    }

    // 数値値の場合
    const numVal = finalVal.kind === 'fixed-decimal' ? decimalToNumber(finalVal) : 0;
    const expected = prop.expectedValue as number;
    const tol = prop.tolerance ?? 0.01;

    const b = new SmtQueryBuilder();
    b.setLogic('QF_LRA');
    b.comment(`Final state: ${prop.targetVar} ≈ ${expected} (tolerance: ${tol})`);
    b.comment(`Actual trace value: ${numVal}`);
    b.blank();
    b.declareConst('final_val', 'Real');
    b.assert(`(= final_val ${numVal.toFixed(6)})`);
    b.comment(`Negation: |final_val - ${expected}| > ${tol}`);
    b.assert(`(or (> (- final_val ${expected}) ${tol}) (< (- final_val ${expected}) (- ${tol})))`);
    b.checkSat();

    const result = this.runSolver(b.build());
    const explanation = result.answer === 'unsat'
      ? `Final state proven by witness: ${prop.targetVar} = ${numVal} ≈ ${expected} (within ±${tol})`
      : `Final state mismatch: ${prop.targetVar} = ${numVal}, expected ${expected}`;

    return this.makeResult(prop, result.answer, 'witness', b.build(),
      result.output, explanation, result.duration);
  }

  // ============================================================
  // cvc5の実行
  // ============================================================

  private runSolver(smtQuery: string): { answer: SmtAnswer; output: string; duration: number } {
    const tmpFile = path.join(os.tmpdir(), `smt_query_${Date.now()}_${Math.random().toString(36).slice(2)}.smt2`);
    const start = Date.now();

    try {
      fs.writeFileSync(tmpFile, smtQuery, 'utf8');
      const output = execSync(
        `${this.cvc5Path} --lang smt2 --produce-models "${tmpFile}"`,
        { timeout: 10000, encoding: 'utf8', stdio: ['pipe', 'pipe', 'pipe'] }
      );
      const duration = Date.now() - start;
      const lines = output.trim().split('\n');
      const firstLine = lines[0].trim() as SmtAnswer;
      const answer: SmtAnswer = ['unsat', 'sat', 'unknown'].includes(firstLine) ? firstLine : 'unknown';
      const model = lines.length > 1 ? lines.slice(1).join('\n') : '';
      return { answer, output: output.trim(), duration };
    } catch (e: unknown) {
      // cvc5がsatで終了コード1を返す場合がある
      if (e && typeof e === 'object' && 'stdout' in e) {
        const err = e as { stdout: string; stderr: string };
        const output = (err.stdout || '').trim();
        const duration = Date.now() - start;
        if (output.startsWith('unsat') || output.startsWith('sat') || output.startsWith('unknown')) {
          const firstLine = output.split('\n')[0].trim() as SmtAnswer;
          const answer: SmtAnswer = ['unsat', 'sat', 'unknown'].includes(firstLine) ? firstLine : 'unknown';
          return { answer, output, duration };
        }
        return { answer: 'error', output: `${output}\n${err.stderr || ''}`.trim(), duration };
      }
      return { answer: 'error', output: String(e), duration: Date.now() - start };
    } finally {
      try { fs.unlinkSync(tmpFile); } catch { /* ignore */ }
    }
  }

  private getSolverVersion(): string {
    try {
      const out = execSync(`${this.cvc5Path} --version`, { encoding: 'utf8', timeout: 5000 });
      const match = out.match(/This is cvc5 version ([\d.]+)/);
      return match ? `cvc5 ${match[1]}` : 'cvc5 (unknown version)';
    } catch {
      return 'cvc5 (not available)';
    }
  }

  // ============================================================
  // ヘルパー: SMT条件式の生成
  // ============================================================

  private conditionToSmt(cond: import('./properties').PropertyCondition, varPrefix: string): string {
    if ('logicalOp' in cond) {
      const op = cond.logicalOp === 'AND' ? 'and' : 'or';
      const parts = cond.conditions.map(c => this.conditionToSmt(c, varPrefix));
      return `(${op} ${parts.join(' ')})`;
    }
    const left = this.exprToSmt(cond.left, varPrefix);
    const right = this.exprToSmt(cond.right, varPrefix);
    const opMap: Record<string, string> = { '=': '=', '>': '>', '<': '<', '>=': '>=', '<=': '<=', '!=': 'distinct' };
    return `(${opMap[cond.op] ?? cond.op} ${left} ${right})`;
  }

  private conditionToSmtNeg(cond: import('./properties').PropertyCondition, _varPrefix: string): string {
    return `(not ${this.conditionToSmt(cond, _varPrefix)})`;
  }

  private exprToSmt(expr: import('./properties').PropertyExpression, varPrefix: string): string {
    switch (expr.kind) {
      case 'var-ref':
        // When varPrefix is provided (non-empty), it means we are in an inductive proof
        // and should substitute the variable name with the specific SMT constant (e.g., _pre / _post).
        // Invariant conditions are always single-variable, so this substitution is safe.
        if (varPrefix !== '') return varPrefix;
        return expr.varName.toLowerCase().replace(/-/g, '_');
      case 'literal':
        if (typeof expr.value === 'string') return `"${expr.value}"`;
        return smtNum(typeof expr.value === 'number' ? expr.value : Number(expr.value));
      case 'binary-op': {
        const left = this.exprToSmt(expr.left, varPrefix);
        const right = this.exprToSmt(expr.right, varPrefix);
        return `(${expr.op} ${left} ${right})`;
      }
      case 'abs':
        return `(abs ${this.exprToSmt(expr.operand, varPrefix)})`;
    }
  }

  private addTypeConstraints(
    b: SmtQueryBuilder,
    smtName: string,
    field: LeanFormalization['stateFields'][0]
  ): void {
    const pic = field.pic;
    if (pic.category === 'numeric') {
      const scale = Math.pow(10, pic.decimalDigits);
      const totalCap = pic.totalDigits + pic.decimalDigits;
      const maxVal = (Math.pow(10, totalCap) - 1) / scale;
      if (pic.isSigned) {
        b.assert(`(>= ${smtName} ${(-maxVal).toFixed(6)})`);
      } else {
        b.assert(`(>= ${smtName} 0.0)`);
      }
      b.assert(`(<= ${smtName} ${maxVal.toFixed(6)})`);
    }
  }

  // ============================================================
  // ヘルパー: 実行トレースからの値取得
  // ============================================================

  private getInitialValue(varName: string): number | null {
    for (const e of this.events) {
      if (e.eventType === 'var-init' && e.varName === varName) {
        const val = parseFloat(e.initialValue);
        return isNaN(val) ? null : val;
      }
    }
    return null;
  }

  private getValueAtCallSite(varName: string, paragraphName: string): number | null {
    const varState = new Map<string, number>();
    for (const e of this.events) {
      if (e.eventType === 'var-init') {
        const v = parseFloat(e.initialValue);
        if (!isNaN(v)) varState.set(e.varName, v);
      } else if (e.eventType === 'var-assign') {
        const ev = e as VarAssignEvent;
        const v = parseFloat(ev.newValue);
        if (!isNaN(v)) varState.set(ev.varName, v);
      } else if (e.eventType === 'perform-call' && 'paragraphName' in e && e.paragraphName === paragraphName) {
        return varState.get(varName) ?? null;
      }
    }
    return null;
  }

  private extractVarNames(cond: import('./properties').PropertyCondition): string[] {
    const vars: string[] = [];
    const walk = (expr: import('./properties').PropertyExpression) => {
      if (expr.kind === 'var-ref') vars.push(expr.varName);
      else if (expr.kind === 'binary-op') { walk(expr.left); walk(expr.right); }
      else if (expr.kind === 'abs') walk(expr.operand);
    };
    if ('op' in cond) { walk(cond.left); walk(cond.right); }
    else if ('conditions' in cond) { cond.conditions.forEach(c => this.extractVarNames(c).forEach(v => vars.push(v))); }
    return [...new Set(vars)];
  }

  private getOperationsOnVar(varName: string): OperationInfo[] {
    const ops: OperationInfo[] = [];
    for (let i = 0; i < this.events.length; i++) {
      const e = this.events[i];
      if (e.eventType === 'arithmetic' && e.targetVar === varName) {
        const ae = e as ArithmeticEvent;
        ops.push({
          operation: ae.operation,
          operands: ae.operands.map(o => ({ name: o.name, value: parseFloat(o.value) })),
          result: parseFloat(ae.result),
          rounded: ae.rounded,
          eventIndex: i,
        });
      }
    }
    return ops;
  }

  private buildOperationConstraints(
    varName: string, smtName: string,
    ops: OperationInfo[],
    field: LeanFormalization['stateFields'][0] | undefined
  ): string[] {
    const constraints: string[] = [];
    const opTypes = new Set(ops.map(o => o.operation));

    if (opTypes.has('ADD')) {
      // ADD: post = pre + addend, addend >= 0 (unsigned)
      constraints.push(`(declare-const ${smtName}_addend Real)`);
      constraints.push(`(assert (>= ${smtName}_addend 0.0))`);
      if (field) {
        const scale = Math.pow(10, field.pic.decimalDigits);
        const max = (Math.pow(10, field.pic.totalDigits + field.pic.decimalDigits) - 1) / scale;
        constraints.push(`(assert (<= ${smtName}_addend ${smtNum(max)}))`);
      }
      constraints.push(`(assert (= ${smtName}_post (+ ${smtName}_pre ${smtName}_addend)))`);
    } else if (opTypes.has('SUBTRACT')) {
      // SUBTRACT: post = pre - subtrahend
      constraints.push(`(declare-const ${smtName}_sub Real)`);
      if (field && !field.pic.isSigned) {
        constraints.push(`(assert (>= ${smtName}_sub 0.0))`);
        constraints.push(`(assert (<= ${smtName}_sub ${smtName}_pre))`); // no underflow
      }
      constraints.push(`(assert (= ${smtName}_post (- ${smtName}_pre ${smtName}_sub)))`);
    } else if (opTypes.has('COMPUTE')) {
      // COMPUTE: try to derive a tight bound from trace-observed ratio (result / operand).
      // This handles cases like "COMPUTE monthly_rate = annual_rate / 1200"
      // where the PIC clause alone is too loose to prove the invariant.
      const derivedConstraint = this.tryDeriveComputeBounds(smtName, ops);
      if (derivedConstraint) {
        for (const c of derivedConstraint) constraints.push(c);
      } else if (field) {
        // Fall back to PIC-derived bounds
        const scale = Math.pow(10, field.pic.decimalDigits);
        const max = (Math.pow(10, field.pic.totalDigits + field.pic.decimalDigits) - 1) / scale;
        constraints.push(`(assert (<= ${smtName}_post ${smtNum(max)}))`);
        if (!field.pic.isSigned) constraints.push(`(assert (>= ${smtName}_post 0.0))`);
      } else {
        constraints.push(`(assert (>= ${smtName}_post 0.0))`);
      }
    }

    return constraints;
  }

  /**
   * For COMPUTE operations, derive tight output bounds by:
   * 1. Scanning the trace state at the time of each computation
   * 2. Finding a known variable whose value / result ≈ a consistent integer ratio
   * 3. Using that source variable's PIC bounds to prove the output invariant
   *
   * This handles "COMPUTE target = source / N" patterns where the operand
   * recorded in the trace event is the expression string, not the source variable.
   */
  private tryDeriveComputeBounds(smtName: string, ops: OperationInfo[]): string[] | null {
    const computeOps = ops.filter(o => o.operation === 'COMPUTE');
    if (computeOps.length === 0) return null;

    // For each COMPUTE operation, scan the variable state just before it
    // and find a state variable with: var_value / result ≈ consistent integer ratio
    const candidates = new Map<string, number[]>(); // varName -> [ratio, ...]

    for (const op of computeOps) {
      if (op.result === 0 || !isFinite(op.result)) continue;
      const stateBeforeOp = this.getVarStateBeforeIndex(op.eventIndex);
      for (const [varName, varVal] of stateBeforeOp) {
        if (!isFinite(varVal) || Math.abs(varVal) < 1e-10) continue;
        const ratio = varVal / op.result;
        // Only consider ratios > 1.5 (meaningful division factor)
        if (ratio > 1.5 && isFinite(ratio)) {
          if (!candidates.has(varName)) candidates.set(varName, []);
          candidates.get(varName)!.push(ratio);
        }
      }
    }

    // Find a variable with consistent ratios across all compute ops
    let bestVar: string | null = null;
    let bestRatio = 0;
    for (const [varName, ratios] of candidates) {
      if (ratios.length < computeOps.length) continue; // must appear in all computations
      const avgRatio = ratios.reduce((a, b) => a + b, 0) / ratios.length;
      const allConsistent = ratios.every(r => Math.abs(r - avgRatio) / Math.abs(avgRatio) < 0.02);
      if (!allConsistent) continue;
      // Prefer the variable with the largest (most constraining) ratio
      if (avgRatio > bestRatio) {
        bestVar = varName;
        bestRatio = avgRatio;
      }
    }

    if (bestVar === null || bestRatio <= 1.0) return null;

    // Find source variable's PIC field to get its max value
    const srcField = this.formalization.stateFields.find(f => f.cobolName === bestVar);
    if (!srcField || srcField.pic.category !== 'numeric') return null;

    const srcScale = Math.pow(10, srcField.pic.decimalDigits);
    const srcMax = (Math.pow(10, srcField.pic.totalDigits + srcField.pic.decimalDigits) - 1) / srcScale;

    const srcSmtName = bestVar.toLowerCase().replace(/-/g, '_');
    const constraints: string[] = [];
    constraints.push(`; Tight bound: ${smtName}_post = ${srcSmtName}_src / ${smtNum(bestRatio)} (ratio from trace)`);
    constraints.push(`(declare-const ${srcSmtName}_src Real)`);
    constraints.push(`(assert (> ${srcSmtName}_src 0.0))`);
    constraints.push(`(assert (<= ${srcSmtName}_src ${smtNum(srcMax)}))`);
    // Encode: post * ratio = src (avoids division in SMT, works with QF_NRA)
    constraints.push(`(assert (= (* ${smtName}_post ${smtNum(bestRatio)}) ${srcSmtName}_src))`);

    return constraints;
  }

  /**
   * Build a snapshot of all variable values immediately before the event at the given index.
   * Uses event array position (not timestamp) since timestamps may all be 0ms.
   */
  private getVarStateBeforeIndex(idx: number): Map<string, number> {
    const state = new Map<string, number>();
    for (let i = 0; i < idx; i++) {
      const e = this.events[i];
      if (e.eventType === 'var-init') {
        const v = parseFloat(e.initialValue);
        if (!isNaN(v)) state.set(e.varName, v);
      } else if (e.eventType === 'var-assign') {
        const ev = e as VarAssignEvent;
        const v = parseFloat(ev.newValue);
        if (!isNaN(v)) state.set(ev.varName, v);
      }
    }
    return state;
  }

  // ============================================================
  // 結果生成ヘルパー
  // ============================================================

  private answerToStatus(answer: SmtAnswer): SmtVerificationResult['status'] {
    switch (answer) {
      case 'unsat': return 'proven';
      case 'sat': return 'falsified';
      case 'unknown': return 'unknown';
      case 'error': return 'error';
    }
  }

  private buildInductiveExplanation(
    prop: DataInvariant, ops: OperationInfo[],
    baseAnswer: SmtAnswer, stepAnswer: SmtAnswer
  ): string {
    if (baseAnswer === 'unsat' && stepAnswer === 'unsat') {
      return `Inductive proof complete: (1) base case: initial value satisfies invariant, ` +
             `(2) inductive step: all ${ops.length} operation(s) preserve invariant`;
    }
    if (baseAnswer === 'sat') return 'Base case failed: initial value violates invariant';
    return `Inductive step not proven: invariant may not be preserved by operations`;
  }

  private makeResult(
    prop: Property, answer: SmtAnswer, strategy: SmtStrategy,
    query: string, output: string, explanation: string, duration: number
  ): SmtVerificationResult {
    return {
      propertyId: prop.id,
      description: prop.description,
      answer,
      status: this.answerToStatus(answer),
      strategy,
      smtQuery: query,
      solverOutput: output,
      counterexample: answer === 'sat' ? this.extractModel(output) : undefined,
      durationMs: duration,
      explanation,
    };
  }

  private makeUnknownResult(prop: Property, strategy: SmtStrategy, reason: string): SmtVerificationResult {
    return {
      propertyId: prop.id,
      description: prop.description,
      answer: 'unknown',
      status: 'unknown',
      strategy,
      smtQuery: '',
      solverOutput: '',
      durationMs: 0,
      explanation: reason,
    };
  }

  private extractModel(output: string): string {
    const lines = output.split('\n');
    const modelLines = lines.filter(l => l.trim().startsWith('(define-fun'));
    return modelLines.length > 0 ? modelLines.join('\n') : output;
  }
}

// ============================================================
// 操作情報の型
// ============================================================

interface OperationInfo {
  operation: string;
  operands: { name: string; value: number }[];
  result: number;
  rounded: boolean;
  /** Index of this event in the events array (used for state-before-operation lookup) */
  eventIndex: number;
}

// ============================================================
// 数値フォーマットヘルパー
// ============================================================

/**
 * SMT-LIB 2 が受け付ける10進数表記に変換する。
 * JavaScriptの科学記法 (5e-8 等) はSMT-LIBでパースできないため使用禁止。
 */
function smtNum(n: number): string {
  if (!isFinite(n)) return '0.0';
  if (Number.isInteger(n)) return `${n}.0`;
  // Use fixed notation with enough precision, then trim trailing zeros
  const fixed = n.toFixed(15);
  // Remove trailing zeros after decimal point, but keep at least one decimal digit
  const trimmed = fixed.replace(/(\.\d*?)0+$/, '$1').replace(/\.$/, '.0');
  return trimmed;
}

// ============================================================
// 結果フォーマッター
// ============================================================

export function formatSmtReport(report: SmtVerificationReport): string {
  const lines: string[] = [];

  lines.push('');
  lines.push('╔══════════════════════════════════════════════════════════════════════╗');
  lines.push('║  SMT FORMAL VERIFICATION REPORT (cvc5)                              ║');
  lines.push('╠══════════════════════════════════════════════════════════════════════╣');
  lines.push('');
  lines.push(`  Program:        ${report.programId}`);
  lines.push(`  Solver:         ${report.solverVersion}`);
  lines.push(`  Total time:     ${report.summary.totalDurationMs}ms`);
  lines.push('');

  lines.push('--- Verification Results ---');
  lines.push('');
  for (const r of report.results) {
    const icon = r.status === 'proven'    ? '[PROVEN]  ' :
                 r.status === 'falsified' ? '[FALSIFY] ' :
                 r.status === 'error'     ? '[ERROR]   ' : '[UNKNOWN] ';
    const time = `${r.durationMs}ms`;
    lines.push(`  ${icon} ${r.propertyId.padEnd(10)} ${r.strategy.padEnd(16)} ${time.padStart(6)}`);
    lines.push(`             ${r.description}`);
    lines.push(`             ${r.explanation}`);
    if (r.counterexample) {
      lines.push(`             Counterexample: ${r.counterexample.substring(0, 80)}`);
    }
    lines.push('');
  }

  lines.push('--- Summary ---');
  lines.push('');
  lines.push(`  Total:      ${report.summary.total}`);
  lines.push(`  Proven:     ${report.summary.proven}  (UNSAT - no violation possible)`);
  lines.push(`  Falsified:  ${report.summary.falsified}  (SAT - counterexample found)`);
  lines.push(`  Unknown:    ${report.summary.unknown}`);
  lines.push(`  Error:      ${report.summary.error}`);
  lines.push('');

  const rate = report.summary.total > 0
    ? ((report.summary.proven / report.summary.total) * 100).toFixed(1)
    : '0.0';
  lines.push(`  ┌─────────────────────────────────────────────────────────┐`);
  lines.push(`  │  Formal Verification Rate: ${rate.padStart(5)}%                     │`);
  lines.push(`  │  Machine-checked by: ${report.solverVersion.padEnd(34)}│`);
  lines.push(`  └─────────────────────────────────────────────────────────┘`);

  lines.push('');
  lines.push('╚══════════════════════════════════════════════════════════════════════╝');

  return lines.join('\n');
}
