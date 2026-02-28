/**
 * POC Main - Proof-Carrying COBOL Modernization Demo
 *
 * 実証する流れ:
 * 1. サンプルCOBOLプログラム（利息計算）をASTとして定義
 * 2. 型安全なインタプリタで実行し、トレースを収集
 * 3. トレースからTypeScriptコードを生成
 * 4. Proof-Carrying: プロパティを定義し検証、Proof Certificateを生成
 * 5. 異なる入力でクロス検証を実行
 * 6. Lean仲介による形式検証: 形式仕様生成、定理証明、統合証明書
 */

import { CobolProgram } from './ast';
import { ExecutionTracer } from './tracer';
import { CobolInterpreter } from './interpreter';
import { generateTypeScript } from './codegen';
import { formatCobolValue } from './types';
import {
  PropertySet, varRef, lit, binOp, abs, cmp, and,
} from './properties';
import { PropertyVerifier } from './verifier';
import { ProofCertificateBuilder, formatCertificate } from './proof-certificate';
import { CrossVerifier, formatCrossVerificationSuite, TestInput } from './cross-verifier';
import {
  FormalVerificationPipeline,
  formatFormalCertificate, formatPhaseResults,
} from './formal-verifier';

// ============================================================
// サンプルCOBOLプログラム: ローン利息計算
// ============================================================
//
// 以下のCOBOLを模倣:
//
//   IDENTIFICATION DIVISION.
//   PROGRAM-ID. LOAN-CALC.
//   DATA DIVISION.
//   WORKING-STORAGE SECTION.
//   01 WS-PRINCIPAL      PIC 9(7)V99 VALUE 100000.00.
//   01 WS-ANNUAL-RATE    PIC 9(2)V9(4) VALUE 3.5000.
//   01 WS-MONTHLY-RATE   PIC 9(2)V9(6).
//   01 WS-MONTHS         PIC 9(3) VALUE 360.
//   01 WS-PAYMENT        PIC 9(7)V99.
//   01 WS-TOTAL-INTEREST PIC 9(9)V99 VALUE 0.
//   01 WS-BALANCE        PIC 9(9)V99.
//   01 WS-INTEREST-AMT   PIC 9(7)V99.
//   01 WS-PRINCIPAL-AMT  PIC 9(7)V99.
//   01 WS-MONTH-CTR      PIC 9(3).
//   01 WS-STATUS         PIC X(10) VALUE "ACTIVE".
//   01 WS-TEMP           PIC 9(9)V9(4).
//   PROCEDURE DIVISION.
//   MAIN-LOGIC.
//       PERFORM CALC-MONTHLY-RATE
//       PERFORM CALC-PAYMENT
//       MOVE WS-PRINCIPAL TO WS-BALANCE
//       PERFORM CALC-AMORTIZATION
//           VARYING WS-MONTH-CTR FROM 1 BY 1
//           UNTIL WS-MONTH-CTR > 12
//       DISPLAY "Total Interest (12 months): " WS-TOTAL-INTEREST
//       IF WS-TOTAL-INTEREST > 3000
//           MOVE "HIGH-INT" TO WS-STATUS
//       ELSE
//           MOVE "LOW-INT" TO WS-STATUS
//       END-IF
//       DISPLAY "Status: " WS-STATUS
//       STOP RUN.
//   CALC-MONTHLY-RATE.
//       COMPUTE WS-MONTHLY-RATE ROUNDED =
//           WS-ANNUAL-RATE / 100 / 12.
//   CALC-PAYMENT.
//       COMPUTE WS-TEMP = WS-MONTHLY-RATE * WS-PRINCIPAL
//       COMPUTE WS-PAYMENT ROUNDED = WS-TEMP.
//   CALC-AMORTIZATION.
//       COMPUTE WS-INTEREST-AMT ROUNDED =
//           WS-BALANCE * WS-MONTHLY-RATE
//       COMPUTE WS-PRINCIPAL-AMT =
//           WS-PAYMENT - WS-INTEREST-AMT
//       SUBTRACT WS-PRINCIPAL-AMT FROM WS-BALANCE
//       ADD WS-INTEREST-AMT TO WS-TOTAL-INTEREST
//       DISPLAY "Month " WS-MONTH-CTR
//              ": Interest=" WS-INTEREST-AMT
//              " Principal=" WS-PRINCIPAL-AMT
//              " Balance=" WS-BALANCE.
//

const loanCalcProgram: CobolProgram = {
  programId: 'LOAN-CALC',
  dataItems: [
    { nodeType: 'data-item', level: 1, name: 'WS-PRINCIPAL', pic: 'S9(7)V99', value: 100000.00, children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-ANNUAL-RATE', pic: '9(2)V9(4)', value: 3.5, children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-MONTHLY-RATE', pic: '9(2)V9(6)', children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-MONTHS', pic: '9(3)', value: 360, children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-PAYMENT', pic: '9(7)V99', children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-TOTAL-INTEREST', pic: '9(9)V99', value: 0, children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-BALANCE', pic: '9(9)V99', children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-INTEREST-AMT', pic: '9(7)V99', children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-PRINCIPAL-AMT', pic: '9(7)V99', children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-MONTH-CTR', pic: '9(3)', children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-STATUS', pic: 'X(10)', value: 'ACTIVE', children: [] },
    { nodeType: 'data-item', level: 1, name: 'WS-TEMP', pic: '9(9)V9(4)', children: [] },
  ],
  paragraphs: [
    {
      name: 'CALC-MONTHLY-RATE',
      statements: [
        {
          stmtType: 'compute',
          target: 'WS-MONTHLY-RATE',
          expression: {
            exprType: 'binary', op: '/',
            left: {
              exprType: 'binary', op: '/',
              left: { exprType: 'variable', name: 'WS-ANNUAL-RATE' },
              right: { exprType: 'literal', value: 100 },
            },
            right: { exprType: 'literal', value: 12 },
          },
          rounded: true,
        },
      ],
    },
    {
      name: 'CALC-PAYMENT',
      statements: [
        {
          stmtType: 'compute',
          target: 'WS-TEMP',
          expression: {
            exprType: 'binary', op: '*',
            left: { exprType: 'variable', name: 'WS-MONTHLY-RATE' },
            right: { exprType: 'variable', name: 'WS-PRINCIPAL' },
          },
          rounded: false,
        },
        {
          stmtType: 'compute',
          target: 'WS-PAYMENT',
          expression: { exprType: 'variable', name: 'WS-TEMP' },
          rounded: true,
        },
      ],
    },
    {
      name: 'CALC-AMORTIZATION',
      statements: [
        {
          stmtType: 'compute',
          target: 'WS-INTEREST-AMT',
          expression: {
            exprType: 'binary', op: '*',
            left: { exprType: 'variable', name: 'WS-BALANCE' },
            right: { exprType: 'variable', name: 'WS-MONTHLY-RATE' },
          },
          rounded: true,
        },
        {
          stmtType: 'compute',
          target: 'WS-PRINCIPAL-AMT',
          expression: {
            exprType: 'binary', op: '-',
            left: { exprType: 'variable', name: 'WS-PAYMENT' },
            right: { exprType: 'variable', name: 'WS-INTEREST-AMT' },
          },
          rounded: false,
        },
        {
          stmtType: 'subtract',
          values: [{ exprType: 'variable', name: 'WS-PRINCIPAL-AMT' }],
          from: 'WS-BALANCE',
          rounded: false,
        },
        {
          stmtType: 'add',
          values: [{ exprType: 'variable', name: 'WS-INTEREST-AMT' }],
          to: 'WS-TOTAL-INTEREST',
          rounded: false,
        },
        {
          stmtType: 'display',
          values: [
            { exprType: 'literal', value: 'Month ' },
            { exprType: 'variable', name: 'WS-MONTH-CTR' },
            { exprType: 'literal', value: ': Interest=' },
            { exprType: 'variable', name: 'WS-INTEREST-AMT' },
            { exprType: 'literal', value: ' Principal=' },
            { exprType: 'variable', name: 'WS-PRINCIPAL-AMT' },
            { exprType: 'literal', value: ' Balance=' },
            { exprType: 'variable', name: 'WS-BALANCE' },
          ],
        },
      ],
    },
  ],
  mainStatements: [
    { stmtType: 'perform', paragraphName: 'CALC-MONTHLY-RATE' },
    { stmtType: 'perform', paragraphName: 'CALC-PAYMENT' },
    {
      stmtType: 'move',
      from: { exprType: 'variable', name: 'WS-PRINCIPAL' },
      to: 'WS-BALANCE',
    },
    {
      stmtType: 'perform-varying',
      paragraphName: 'CALC-AMORTIZATION',
      variable: 'WS-MONTH-CTR',
      from: { exprType: 'literal', value: 1 },
      by: { exprType: 'literal', value: 1 },
      until: {
        condType: 'comparison',
        op: '>',
        left: { exprType: 'variable', name: 'WS-MONTH-CTR' },
        right: { exprType: 'literal', value: 12 },
      },
    },
    {
      stmtType: 'display',
      values: [
        { exprType: 'literal', value: 'Total Interest (12 months): ' },
        { exprType: 'variable', name: 'WS-TOTAL-INTEREST' },
      ],
    },
    {
      stmtType: 'if',
      condition: {
        condType: 'comparison',
        op: '>',
        left: { exprType: 'variable', name: 'WS-TOTAL-INTEREST' },
        right: { exprType: 'literal', value: 3000 },
      },
      thenBlock: [
        {
          stmtType: 'move',
          from: { exprType: 'literal', value: 'HIGH-INT' },
          to: 'WS-STATUS',
        },
      ],
      elseBlock: [
        {
          stmtType: 'move',
          from: { exprType: 'literal', value: 'LOW-INT' },
          to: 'WS-STATUS',
        },
      ],
    },
    {
      stmtType: 'display',
      values: [
        { exprType: 'literal', value: 'Status: ' },
        { exprType: 'variable', name: 'WS-STATUS' },
      ],
    },
    { stmtType: 'stop-run' },
  ],
};

// ============================================================
// Proof-Carrying: ローン計算プログラムのプロパティ定義
// ============================================================
//
// これらのプロパティはビジネスルールや数学的性質を表現する。
// モダナイゼーション後もこれらが保持されることを保証する。

const loanCalcProperties: PropertySet = {
  programId: 'LOAN-CALC',
  version: '1.0.0',
  createdAt: new Date().toISOString(),
  properties: [
    // --- ビジネスルール不変条件 ---
    {
      propertyType: 'data-invariant',
      id: 'INV-01',
      description: 'WS-TOTAL-INTEREST は常に 0 以上（利息はマイナスにならない）',
      targetVar: 'WS-TOTAL-INTEREST',
      condition: cmp('>=', varRef('WS-TOTAL-INTEREST'), lit(0)),
      checkAt: 'every-assignment',
    },
    {
      propertyType: 'data-invariant',
      id: 'INV-02',
      description: 'WS-BALANCE は常に 0 以上（残高はマイナスにならない）',
      targetVar: 'WS-BALANCE',
      condition: cmp('>=', varRef('WS-BALANCE'), lit(0)),
      checkAt: 'every-assignment',
    },
    {
      propertyType: 'data-invariant',
      id: 'INV-03',
      description: 'WS-MONTHLY-RATE は 1 未満（月利が100%を超えることはない）',
      targetVar: 'WS-MONTHLY-RATE',
      condition: cmp('<', varRef('WS-MONTHLY-RATE'), lit(1)),
      checkAt: 'every-assignment',
    },

    // --- 事前条件 ---
    {
      propertyType: 'precondition',
      id: 'PRE-01',
      description: 'CALC-MONTHLY-RATE 呼出前: WS-ANNUAL-RATE > 0',
      paragraphName: 'CALC-MONTHLY-RATE',
      condition: cmp('>', varRef('WS-ANNUAL-RATE'), lit(0)),
    },
    {
      propertyType: 'precondition',
      id: 'PRE-02',
      description: 'CALC-PAYMENT 呼出前: WS-MONTHLY-RATE > 0',
      paragraphName: 'CALC-PAYMENT',
      condition: cmp('>', varRef('WS-MONTHLY-RATE'), lit(0)),
    },

    // --- 事後条件 ---
    {
      propertyType: 'postcondition',
      id: 'POST-01',
      description: 'CALC-MONTHLY-RATE 実行後: WS-MONTHLY-RATE > 0',
      paragraphName: 'CALC-MONTHLY-RATE',
      condition: cmp('>', varRef('WS-MONTHLY-RATE'), lit(0)),
    },
    {
      propertyType: 'postcondition',
      id: 'POST-02',
      description: 'CALC-PAYMENT 実行後: WS-PAYMENT > 0',
      paragraphName: 'CALC-PAYMENT',
      condition: cmp('>', varRef('WS-PAYMENT'), lit(0)),
    },

    // --- 変数間の関係性 ---
    {
      propertyType: 'relational',
      id: 'REL-01',
      description: 'CALC-AMORTIZATION 後: WS-PRINCIPAL-AMT + WS-INTEREST-AMT ≈ WS-PAYMENT',
      condition: cmp('=',
        binOp('+', varRef('WS-PRINCIPAL-AMT'), varRef('WS-INTEREST-AMT')),
        varRef('WS-PAYMENT')
      ),
      tolerance: 0.01,
      checkAfterParagraph: 'CALC-AMORTIZATION',
    },

    // --- 算術精度の保証 ---
    {
      propertyType: 'precision',
      id: 'PREC-01',
      description: 'WS-MONTHLY-RATE は ROUNDED モードで計算されること',
      targetVar: 'WS-MONTHLY-RATE',
      minDecimalPlaces: 6,
      roundingMode: 'must-round',
    },
    {
      propertyType: 'precision',
      id: 'PREC-02',
      description: 'WS-INTEREST-AMT は ROUNDED モードで計算されること',
      targetVar: 'WS-INTEREST-AMT',
      minDecimalPlaces: 2,
      roundingMode: 'must-round',
    },

    // --- ループ上限保証 ---
    {
      propertyType: 'loop-bound',
      id: 'LOOP-01',
      description: 'CALC-AMORTIZATION ループは 12 回で終了する',
      paragraphName: 'CALC-AMORTIZATION',
      maxIterations: 12,
    },

    // --- 最終状態の検証 ---
    {
      propertyType: 'final-state',
      id: 'FINAL-01',
      description: 'プログラム終了時: WS-STATUS は "HIGH-INT" または "LOW-INT"',
      targetVar: 'WS-STATUS',
      expectedValue: 'HIGH-INT',  // デフォルト入力ではHIGH-INT
    },

    // --- 出力同値性 ---
    {
      propertyType: 'output-equivalence',
      id: 'OUT-01',
      description: 'DISPLAY出力がモダナイゼーション前後で一致すること',
      numericTolerance: 0.01,
    },
  ],
};

// ============================================================
// メイン実行
// ============================================================

function main(): void {
  console.log('╔═══════════════════════════════════════════════════════════════╗');
  console.log('║  Proof-Carrying COBOL Modernization - POC                     ║');
  console.log('║  プロパティ保証付きCOBOLモダナイゼーション                     ║');
  console.log('╚═══════════════════════════════════════════════════════════════╝');
  console.log('');

  // ========================================
  // Phase 1: 型安全なインタプリタで実行
  // ========================================
  console.log('━━━ Phase 1: Execute COBOL in Type-Safe Interpreter ━━━');
  console.log('');

  const tracer = new ExecutionTracer();
  const interpreter = new CobolInterpreter(tracer);
  const result = interpreter.execute(loanCalcProgram);

  console.log('--- Program Output (DISPLAY) ---');
  for (const line of result.displayOutput) {
    console.log(`  ${line}`);
  }
  console.log('');

  console.log('--- Final Variable States ---');
  for (const [name, value] of result.variables) {
    console.log(`  ${name.padEnd(20)} = ${formatCobolValue(value).padStart(15)}  [${value.kind}]`);
  }
  console.log('');

  // ========================================
  // Phase 2: 実行トレースの分析
  // ========================================
  console.log('━━━ Phase 2: Analyze Execution Traces ━━━');
  console.log('');

  const summary = tracer.getSummary();
  console.log(`  Total trace events:     ${summary.totalEvents}`);
  console.log(`  Total statements:       ${summary.totalStatements}`);
  console.log(`  Variables tracked:      ${summary.variableCount}`);
  console.log(`  Assignments recorded:   ${summary.assignmentCount}`);
  console.log(`  Arithmetic operations:  ${summary.arithmeticCount}`);
  console.log(`  Branch decisions:       ${summary.branchCount}`);
  console.log(`  PERFORM calls:          ${summary.performCallCount}`);
  console.log(`  Loop iterations:        ${summary.loopIterationCount}`);
  console.log(`  Rounding operations:    ${summary.roundingOperations}`);
  console.log('');

  // ========================================
  // Phase 3: トレースからTypeScriptを生成
  // ========================================
  console.log('━━━ Phase 3: Generate TypeScript from Traces ━━━');
  console.log('');

  const generated = generateTypeScript(loanCalcProgram, tracer.getEvents(), summary);

  console.log('--- Generation Insights ---');
  for (const insight of generated.insights) {
    console.log(`  ${insight}`);
  }
  console.log('');

  // ========================================
  // Phase 4: Proof-Carrying - プロパティ検証
  // ========================================
  console.log('━━━ Phase 4: Proof-Carrying Property Verification ━━━');
  console.log('');
  console.log(`  Property Set: "${loanCalcProperties.programId}" v${loanCalcProperties.version}`);
  console.log(`  Total Properties: ${loanCalcProperties.properties.length}`);
  console.log('');

  // プロパティ一覧を表示
  console.log('--- Defined Properties ---');
  for (const prop of loanCalcProperties.properties) {
    console.log(`  [${prop.propertyType.padEnd(20)}] ${prop.id}: ${prop.description}`);
  }
  console.log('');

  // 検証実行
  console.log('--- Verification Results ---');
  console.log('');

  const verifier = new PropertyVerifier(
    tracer.getEvents(),
    result.variables,
    result.displayOutput
  );
  const report = verifier.verify(loanCalcProperties);

  for (const r of report.results) {
    const icon = r.status === 'passed' ? '[PASS]' : r.status === 'failed' ? '[FAIL]' : '[SKIP]';
    console.log(`  ${icon} ${r.propertyId}: ${r.description}`);
    console.log(`         ${r.message}`);
    if (r.violations.length > 0) {
      for (const v of r.violations) {
        console.log(`         ! ${v.detail}`);
        for (const [k, val] of Object.entries(v.actualValues)) {
          console.log(`           ${k} = ${val}`);
        }
      }
    }
  }
  console.log('');
  console.log(`  Summary: ${report.summary.passed}/${report.summary.total} passed, ${report.summary.failed} failed, ${report.summary.skipped} skipped`);
  console.log('');

  // ========================================
  // Phase 5: Proof Certificate 生成
  // ========================================
  console.log('━━━ Phase 5: Generate Proof Certificate ━━━');

  const stateMap = new Map<string, string>();
  for (const [name, value] of result.variables) {
    stateMap.set(name, formatCobolValue(value));
  }

  const certificate = new ProofCertificateBuilder(
    loanCalcProgram.programId,
    'TypeScript',
    loanCalcProperties,
    report
  )
    .withSourceOutput(result.displayOutput)
    .withSourceState(stateMap)
    .build();

  console.log(formatCertificate(certificate));

  // ========================================
  // Phase 6: クロス検証（異なる入力データ）
  // ========================================
  console.log('━━━ Phase 6: Cross-Verification with Multiple Inputs ━━━');
  console.log('');

  const testInputs: TestInput[] = [
    {
      name: 'Low Rate (1%)',
      overrides: new Map<string, number | string>([
        ['WS-ANNUAL-RATE', 1.0],
        ['WS-PRINCIPAL', 50000],
      ]),
    },
    {
      name: 'High Rate (8%)',
      overrides: new Map<string, number | string>([
        ['WS-ANNUAL-RATE', 8.0],
        ['WS-PRINCIPAL', 200000],
      ]),
    },
    {
      name: 'Small Loan',
      overrides: new Map<string, number | string>([
        ['WS-ANNUAL-RATE', 5.0],
        ['WS-PRINCIPAL', 10000],
      ]),
    },
  ];

  const crossVerifier = new CrossVerifier(loanCalcProgram, loanCalcProperties);
  const suite = crossVerifier.verifyWithTestInputs(testInputs);

  console.log(formatCrossVerificationSuite(suite));

  // ========================================
  // Phase 7: Lean仲介による形式検証
  // ========================================
  console.log('━━━ Phase 7: Lean-Mediated Formal Verification ━━━');
  console.log('');
  console.log('  Lean 4定理証明系を中間言語として使い、プロパティの');
  console.log('  形式的証明と変換正当性を統一的に扱う体系を構築する。');
  console.log('');

  const formalPipeline = new FormalVerificationPipeline(loanCalcProgram, loanCalcProperties);
  const formalExecution = formalPipeline.execute();

  // Phase実行結果
  console.log(formatPhaseResults(formalExecution.phases));

  // Phase 7a: Lean形式仕様の概要
  console.log('━━━ Phase 7a: Lean 4 Formal Specification ━━━');
  console.log('');
  const leanSpec = formalExecution.certificate.leanFormalization;
  console.log(`  Program State fields:  ${leanSpec.stats.totalFields}`);
  console.log(`  Semantic functions:    ${leanSpec.stats.totalFunctions}`);
  console.log(`  Type constraints:      ${leanSpec.stats.totalConstraints}`);
  console.log(`  Lean source lines:     ${leanSpec.stats.totalLeanLines}`);
  console.log('');

  // State構造体のフィールド表示
  console.log('  --- Lean State Fields ---');
  for (const field of leanSpec.stateFields) {
    console.log(`    ${field.cobolName.padEnd(20)} → ${field.leanName.padEnd(20)} : ${field.leanType}`);
  }
  console.log('');

  // Type Constraints表示
  console.log('  --- Type Constraints (PIC clause invariants) ---');
  for (const tc of leanSpec.typeConstraints) {
    console.log(`    [${tc.constraintType.padEnd(9)}] ${tc.description}`);
  }
  console.log('');

  // Lean Source抜粋（先頭部分）
  console.log('  --- Lean 4 Source (excerpt) ---');
  const leanLines = leanSpec.leanSource.split('\n');
  const excerptEnd = Math.min(40, leanLines.length);
  for (let i = 0; i < excerptEnd; i++) {
    console.log(`    ${leanLines[i]}`);
  }
  if (leanLines.length > excerptEnd) {
    console.log(`    ... (${leanLines.length - excerptEnd} more lines)`);
  }
  console.log('');

  // Phase 7b: Lean定理と証明
  console.log('━━━ Phase 7b: Lean Theorems and Proofs ━━━');
  console.log('');
  const proofResult = formalExecution.certificate.formalProofs;
  console.log(`  Total theorems:     ${proofResult.stats.totalTheorems}`);
  console.log(`  Formal coverage:    ${(proofResult.stats.formalProofCoverage * 100).toFixed(1)}%`);
  console.log(`  Runtime witnesses:  ${proofResult.stats.totalWitnesses}`);
  console.log('');

  // 各定理の概要
  console.log('  --- Theorems ---');
  for (const thm of proofResult.theorems) {
    const levelIcon =
      thm.proofLevel === 'decide' ? '[D]' :
      thm.proofLevel === 'induction' ? '[I]' :
      thm.proofLevel === 'refinement' ? '[R]' : '[A]';
    console.log(`  ${levelIcon} ${thm.theoremName.padEnd(40)} ${thm.strategy.padEnd(18)} witnesses: ${thm.witnesses.length}`);
    if (thm.witnesses.length > 0) {
      const first = thm.witnesses[0];
      console.log(`      witness: ${first.varName} = ${first.value} (${first.witnessType})`);
    }
  }
  console.log('');

  // Proof Level分布
  console.log('  --- Proof Level Distribution ---');
  for (const [level, count] of Object.entries(proofResult.stats.byLevel)) {
    if (count > 0) {
      const bar = '█'.repeat(count) + '░'.repeat(Math.max(0, 10 - count));
      console.log(`    ${level.padEnd(12)} ${bar} ${count}`);
    }
  }
  console.log('');

  // Phase 7c: 変換正当性
  console.log('━━━ Phase 7c: Transformation Correctness ━━━');
  console.log('');
  const transSummary = formalExecution.certificate.transformationSummary;
  console.log(`  ${transSummary.sourceLang} → ${transSummary.targetLang}`);
  console.log(`  Equivalence status:   ${transSummary.equivalenceStatus}`);
  console.log(`  Properties preserved: ${transSummary.preservedProperties}/${transSummary.totalProperties}`);
  console.log(`  Bisimulation via:`);
  for (const comp of transSummary.bisimulationComponents) {
    console.log(`    - ${comp}`);
  }
  console.log('');

  // Phase 7d: 統合証明書
  console.log('━━━ Phase 7d: Unified Formal Proof Certificate ━━━');
  console.log(formatFormalCertificate(formalExecution.certificate));

  // ========================================
  // 最終サマリー
  // ========================================
  console.log('╔═══════════════════════════════════════════════════════════════════════╗');
  console.log('║  Proof-Carrying COBOL Modernization - Extended Summary               ║');
  console.log('║  (with Lean-Mediated Formal Verification)                            ║');
  console.log('╠═══════════════════════════════════════════════════════════════════════╣');
  console.log('║                                                                       ║');
  console.log('║  1. Property Definition (プロパティ定義):                             ║');
  console.log(`║     ${String(loanCalcProperties.properties.length).padStart(2)} properties defined across 8 categories`.padEnd(68) + '║');
  console.log('║                                                                       ║');
  console.log('║  2. Runtime Verification (ランタイム検証):                            ║');
  console.log(`║     ${report.summary.passed}/${report.summary.total} properties verified on original COBOL`.padEnd(68) + '║');
  console.log('║                                                                       ║');
  console.log('║  3. Lean Formal Specification (形式仕様):                             ║');
  console.log(`║     ${leanSpec.stats.totalLeanLines} lines of Lean 4 code generated`.padEnd(68) + '║');
  console.log(`║     ${leanSpec.stats.totalFunctions} semantic functions, ${leanSpec.stats.totalConstraints} type constraints`.padEnd(68) + '║');
  console.log('║                                                                       ║');
  console.log('║  4. Formal Proofs (形式証明):                                        ║');
  console.log(`║     ${proofResult.stats.totalTheorems} theorems generated`.padEnd(68) + '║');
  console.log(`║     ${(proofResult.stats.formalProofCoverage * 100).toFixed(0)}% formal proof coverage`.padEnd(68) + '║');
  console.log(`║     ${proofResult.stats.totalWitnesses} runtime witnesses integrated`.padEnd(68) + '║');
  console.log('║                                                                       ║');
  console.log('║  5. Transformation Correctness (変換正当性):                          ║');
  console.log(`║     Semantic equivalence: ${transSummary.equivalenceStatus}`.padEnd(68) + '║');
  console.log(`║     ${transSummary.preservedProperties}/${transSummary.totalProperties} properties preserved by bisimulation`.padEnd(68) + '║');
  console.log('║                                                                       ║');
  console.log('║  6. Unified Confidence (統合信頼性):                                  ║');
  console.log(`║     ${formalExecution.certificate.confidenceLevel.toUpperCase()}`.padEnd(68) + '║');
  console.log('║                                                                       ║');
  console.log('║  Enhanced Proof-Carrying Flow:                                        ║');
  console.log('║                                                                       ║');
  console.log('║  COBOL Source ──────────────────────────────────────────────┐          ║');
  console.log('║    │                                                        │          ║');
  console.log('║    ├─→ [Interpreter] ─→ Execution Traces ─→ Runtime Proof   │          ║');
  console.log('║    │                                                        │          ║');
  console.log('║    ├─→ [Lean IR Gen] ─→ Lean 4 Formal Spec                 │          ║');
  console.log('║    │                       │                                │          ║');
  console.log('║    │                       ├─ Property Theorems             │          ║');
  console.log('║    │                       ├─ Type Constraints              │          ║');
  console.log('║    │                       └─ Bisimulation Proof            │          ║');
  console.log('║    │                                                        │          ║');
  console.log('║    └─→ [CodeGen] ─→ TypeScript ─→ Preservation Proof       │          ║');
  console.log('║                                                             │          ║');
  console.log('║    ════════════════════════════════════════════════════      │          ║');
  console.log('║    ▼ Unified Formal Proof Certificate                       │          ║');
  console.log('║      Runtime + Formal + Bisimulation = Stronger Guarantee   │          ║');
  console.log('║                                                                       ║');
  console.log('╚═══════════════════════════════════════════════════════════════════════╝');
}

main();
