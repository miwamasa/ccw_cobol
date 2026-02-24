/**
 * POC Main - Instrumented COBOL Interpreter Demo
 * 
 * 実証する流れ:
 * 1. サンプルCOBOLプログラム（利息計算）をASTとして定義
 * 2. 型安全なインタプリタで実行し、トレースを収集
 * 3. トレースからTypeScriptコードを生成
 * 4. 結果を比較・分析
 */

import { CobolProgram } from './ast';
import { ExecutionTracer } from './tracer';
import { CobolInterpreter } from './interpreter';
import { generateTypeScript } from './codegen';
import { formatCobolValue } from './types';

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
        // COMPUTE WS-INTEREST-AMT ROUNDED = WS-BALANCE * WS-MONTHLY-RATE
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
        // COMPUTE WS-PRINCIPAL-AMT = WS-PAYMENT - WS-INTEREST-AMT
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
        // SUBTRACT WS-PRINCIPAL-AMT FROM WS-BALANCE
        {
          stmtType: 'subtract',
          values: [{ exprType: 'variable', name: 'WS-PRINCIPAL-AMT' }],
          from: 'WS-BALANCE',
          rounded: false,
        },
        // ADD WS-INTEREST-AMT TO WS-TOTAL-INTEREST
        {
          stmtType: 'add',
          values: [{ exprType: 'variable', name: 'WS-INTEREST-AMT' }],
          to: 'WS-TOTAL-INTEREST',
          rounded: false,
        },
        // DISPLAY
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
    // PERFORM CALC-MONTHLY-RATE
    { stmtType: 'perform', paragraphName: 'CALC-MONTHLY-RATE' },
    // PERFORM CALC-PAYMENT
    { stmtType: 'perform', paragraphName: 'CALC-PAYMENT' },
    // MOVE WS-PRINCIPAL TO WS-BALANCE
    {
      stmtType: 'move',
      from: { exprType: 'variable', name: 'WS-PRINCIPAL' },
      to: 'WS-BALANCE',
    },
    // PERFORM CALC-AMORTIZATION VARYING WS-MONTH-CTR FROM 1 BY 1 UNTIL WS-MONTH-CTR > 12
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
    // DISPLAY "Total Interest..."
    {
      stmtType: 'display',
      values: [
        { exprType: 'literal', value: 'Total Interest (12 months): ' },
        { exprType: 'variable', name: 'WS-TOTAL-INTEREST' },
      ],
    },
    // IF WS-TOTAL-INTEREST > 3000
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
    // DISPLAY "Status: " WS-STATUS
    {
      stmtType: 'display',
      values: [
        { exprType: 'literal', value: 'Status: ' },
        { exprType: 'variable', name: 'WS-STATUS' },
      ],
    },
    // STOP RUN
    { stmtType: 'stop-run' },
  ],
};

// ============================================================
// メイン実行
// ============================================================

function main(): void {
  console.log('╔══════════════════════════════════════════════════════════════╗');
  console.log('║  COBOL Instrumented Interpreter - Proof of Concept          ║');
  console.log('║  型安全な計装付きCOBOLインタプリタによるモダナイゼーション   ║');
  console.log('╚══════════════════════════════════════════════════════════════╝');
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

  // 分岐カバレッジ
  console.log('  Branch Coverage:');
  for (const [cond, cov] of Object.entries(summary.branchCoverage)) {
    const total = cov.then + cov.else;
    console.log(`    "${cond}"`);
    console.log(`      THEN: ${cov.then}/${total}  ELSE: ${cov.else}/${total}`);
    if (cov.then === 0 || cov.else === 0) {
      console.log(`      ⚠️  Only one branch exercised - need more test data!`);
    }
  }
  console.log('');

  // 型変換の検出
  if (Object.keys(summary.typeTransitions).length > 0) {
    console.log('  Type Conversions Detected:');
    for (const [varName, transitions] of Object.entries(summary.typeTransitions)) {
      for (const t of transitions) {
        console.log(`    ${varName}: ${t}`);
      }
    }
    console.log('');
  }

  // パラグラフ呼び出し
  console.log('  Paragraph Call Counts:');
  for (const [name, count] of Object.entries(summary.paragraphCalls)) {
    console.log(`    ${name}: ${count} calls`);
  }
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

  console.log('--- Generated TypeScript Code ---');
  console.log('');
  console.log(generated.typescript);
  console.log('');

  // ========================================
  // Phase 4: トレースのサンプル出力
  // ========================================
  console.log('━━━ Phase 4: Sample Trace Events (first 15) ━━━');
  console.log('');
  const events = tracer.getEvents();
  for (let i = 0; i < Math.min(15, events.length); i++) {
    const e = events[i];
    console.log(`  [${i}] ${e.eventType} @ ${e.timestamp}ms`);
    switch (e.eventType) {
      case 'var-init':
        console.log(`      ${e.varName} = ${e.initialValue} (${e.cobolType})`);
        break;
      case 'var-assign':
        console.log(`      ${e.varName}: ${e.previousValue} → ${e.newValue}`);
        if (e.sourceInfo) console.log(`      conversion: ${e.sourceInfo.conversionApplied}`);
        break;
      case 'arithmetic':
        console.log(`      ${e.operation}: ${e.operands.map(o => `${o.name}=${o.value}`).join(', ')} → ${e.result}`);
        if (e.roundingDetail) console.log(`      rounding: ${e.roundingDetail.rawResult} → ${e.roundingDetail.roundedResult}`);
        break;
      case 'branch':
        console.log(`      ${e.condition} => ${e.branchTaken}`);
        break;
      case 'perform-call':
        console.log(`      → ${e.paragraphName} (depth: ${e.callDepth})`);
        break;
      case 'loop-iteration':
        console.log(`      ${e.paragraphName} iter ${e.iteration}: ${e.loopVar}=${e.currentValue}`);
        break;
    }
  }
  console.log(`  ... (${events.length - 15} more events)`);
  console.log('');

  // ========================================
  // サマリー
  // ========================================
  console.log('╔══════════════════════════════════════════════════════════════╗');
  console.log('║  POC Summary                                                ║');
  console.log('╠══════════════════════════════════════════════════════════════╣');
  console.log('║                                                              ║');
  console.log('║  ✅ 型安全なCOBOLランタイム:                                ║');
  console.log('║     - FixedDecimal / Alphanumeric をDiscriminated Unionで表現║');
  console.log('║     - PIC句の暗黙的型情報を明示的な型として捕捉              ║');
  console.log('║     - 固定小数点演算の丸め挙動を完全に追跡                   ║');
  console.log('║                                                              ║');
  console.log('║  ✅ 実行トレース収集:                                       ║');
  console.log(`║     - ${summary.totalEvents} events captured across ${summary.totalStatements} statements`.padEnd(63) + '║');
  console.log('║     - 変数の型遷移、分岐パス、算術精度を記録                 ║');
  console.log('║     - 分岐カバレッジの不足を自動検出                         ║');
  console.log('║                                                              ║');
  console.log('║  ✅ トレースからのコード生成:                               ║');
  console.log('║     - 実行トレースに基づく型推論でTypeScript型を決定          ║');
  console.log('║     - 精度要件の自動検出（BigDecimal必要箇所の特定）         ║');
  console.log('║     - 未カバー分岐の警告（追加テストデータの必要性）         ║');
  console.log('║                                                              ║');
  console.log('║  → 実プロダクトでは、このトレース情報をLLMに入力し、         ║');
  console.log('║    より洗練されたコード生成を行う                            ║');
  console.log('╚══════════════════════════════════════════════════════════════╝');
}

main();
