/**
 * Test Suite - Instrumented COBOL Interpreter
 * 
 * テストカテゴリ:
 * 1. 型システムのテスト（PIC句解析、固定小数点精度）
 * 2. インタプリタ実行のテスト（MOVE、算術、分岐）
 * 3. トレース収集のテスト（イベントが正しく記録されるか）
 * 4. 暗黙的型変換のテスト（COBOL特有の変換ルール）
 */

import { parsePic, makeFixedDecimal, makeAlphanumeric, decimalToNumber, formatCobolValue, PicClause } from '../src/types';
import { CobolProgram, DataItemDef } from '../src/ast';
import { ExecutionTracer, VarInitEvent, ArithmeticEvent, BranchEvent, VarAssignEvent } from '../src/tracer';
import { CobolInterpreter } from '../src/interpreter';

// ============================================================
// テストフレームワーク（軽量）
// ============================================================

let totalTests = 0;
let passedTests = 0;
let failedTests = 0;
const failures: string[] = [];

function describe(name: string, fn: () => void): void {
  console.log(`\n📋 ${name}`);
  fn();
}

function it(name: string, fn: () => void): void {
  totalTests++;
  try {
    fn();
    passedTests++;
    console.log(`  ✅ ${name}`);
  } catch (e) {
    failedTests++;
    const msg = e instanceof Error ? e.message : String(e);
    console.log(`  ❌ ${name}`);
    console.log(`     ${msg}`);
    failures.push(`${name}: ${msg}`);
  }
}

function assert(condition: boolean, message: string): void {
  if (!condition) throw new Error(`Assertion failed: ${message}`);
}

function assertEqual<T>(actual: T, expected: T, label: string): void {
  if (actual !== expected) {
    throw new Error(`${label}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

function assertApprox(actual: number, expected: number, epsilon: number, label: string): void {
  if (Math.abs(actual - expected) > epsilon) {
    throw new Error(`${label}: expected ~${expected}, got ${actual} (diff: ${Math.abs(actual - expected)})`);
  }
}

// ============================================================
// 1. 型システムのテスト
// ============================================================

describe('PIC Clause Parser', () => {
  it('should parse simple numeric PIC 9(5)', () => {
    const pic = parsePic('9(5)');
    assertEqual(pic.category, 'numeric', 'category');
    assertEqual(pic.totalDigits, 5, 'totalDigits');
    assertEqual(pic.decimalDigits, 0, 'decimalDigits');
    assertEqual(pic.isSigned, false, 'isSigned');
  });

  it('should parse signed decimal PIC S9(5)V99', () => {
    const pic = parsePic('S9(5)V99');
    assertEqual(pic.category, 'numeric', 'category');
    assertEqual(pic.totalDigits, 5, 'totalDigits');
    assertEqual(pic.decimalDigits, 2, 'decimalDigits');
    assertEqual(pic.isSigned, true, 'isSigned');
  });

  it('should parse PIC with V and repeat: 9(2)V9(4)', () => {
    const pic = parsePic('9(2)V9(4)');
    assertEqual(pic.totalDigits, 2, 'totalDigits');
    assertEqual(pic.decimalDigits, 4, 'decimalDigits');
  });

  it('should parse alphanumeric PIC X(10)', () => {
    const pic = parsePic('X(10)');
    assertEqual(pic.category, 'alphanumeric', 'category');
    assertEqual(pic.size, 10, 'size');
  });

  it('should parse simple PIC 999', () => {
    const pic = parsePic('999');
    assertEqual(pic.totalDigits, 3, 'totalDigits');
    assertEqual(pic.decimalDigits, 0, 'decimalDigits');
  });
});

describe('Fixed Decimal Values', () => {
  it('should create decimal with correct precision', () => {
    const pic = parsePic('9(5)V99');
    const val = makeFixedDecimal(12345.67, pic);
    assertEqual(val.kind, 'fixed-decimal', 'kind');
    assertEqual(val.scale, 2, 'scale');
    assertApprox(decimalToNumber(val), 12345.67, 0.001, 'value');
  });

  it('should truncate excess decimal digits', () => {
    const pic = parsePic('9(5)V99');
    const val = makeFixedDecimal(123.456, pic);
    // PIC V99 = 2 decimal places → 123.456 should truncate to 123.45
    assertApprox(decimalToNumber(val), 123.45, 0.001, 'truncated value');
  });

  it('should handle zero correctly', () => {
    const pic = parsePic('9(7)V99');
    const val = makeFixedDecimal(0, pic);
    assertEqual(decimalToNumber(val), 0, 'zero value');
  });

  it('should format decimal for display', () => {
    const pic = parsePic('9(5)V99');
    const val = makeFixedDecimal(100.50, pic);
    const formatted = formatCobolValue(val);
    assert(formatted.includes('100.50'), `Expected "100.50" in "${formatted}"`);
  });
});

describe('Alphanumeric Values', () => {
  it('should pad with spaces to declared length', () => {
    const val = makeAlphanumeric('ABC', 10);
    assertEqual(val.bytes.length, 10, 'length');
    assertEqual(val.bytes, 'ABC       ', 'padded value');
  });

  it('should truncate excess characters', () => {
    const val = makeAlphanumeric('HELLO WORLD', 5);
    assertEqual(val.bytes, 'HELLO', 'truncated value');
  });
});

// ============================================================
// 2. インタプリタ実行のテスト
// ============================================================

function makeSimpleProgram(
  dataItems: DataItemDef[],
  mainStatements: CobolProgram['mainStatements'],
  paragraphs: CobolProgram['paragraphs'] = []
): CobolProgram {
  return {
    programId: 'TEST-PROG',
    dataItems,
    paragraphs,
    mainStatements,
  };
}

describe('MOVE Statement', () => {
  it('should move numeric literal to numeric variable', () => {
    const prog = makeSimpleProgram(
      [{ nodeType: 'data-item', level: 1, name: 'WS-A', pic: '9(5)V99', value: 0, children: [] }],
      [{ stmtType: 'move', from: { exprType: 'literal', value: 12345.67 }, to: 'WS-A' }]
    );
    const tracer = new ExecutionTracer();
    const result = new CobolInterpreter(tracer).execute(prog);
    const val = result.variables.get('WS-A');
    assert(val !== undefined && val.kind === 'fixed-decimal', 'should be fixed-decimal');
    assertApprox(decimalToNumber(val as any), 12345.67, 0.01, 'moved value');
  });

  it('should move string literal to alphanumeric variable', () => {
    const prog = makeSimpleProgram(
      [{ nodeType: 'data-item', level: 1, name: 'WS-NAME', pic: 'X(10)', value: '', children: [] }],
      [{ stmtType: 'move', from: { exprType: 'literal', value: 'HELLO' }, to: 'WS-NAME' }]
    );
    const tracer = new ExecutionTracer();
    const result = new CobolInterpreter(tracer).execute(prog);
    const val = result.variables.get('WS-NAME');
    assert(val !== undefined && val.kind === 'alphanumeric', 'should be alphanumeric');
    assertEqual((val as any).bytes, 'HELLO     ', 'padded string');
  });

  it('should track type conversion in trace when moving numeric to alphanumeric', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-NUM', pic: '9(3)', value: 42, children: [] },
        { nodeType: 'data-item', level: 1, name: 'WS-STR', pic: 'X(5)', value: '', children: [] },
      ],
      [{ stmtType: 'move', from: { exprType: 'variable', name: 'WS-NUM' }, to: 'WS-STR' }]
    );
    const tracer = new ExecutionTracer();
    new CobolInterpreter(tracer).execute(prog);
    const assigns = tracer.getEvents().filter(e => e.eventType === 'var-assign') as VarAssignEvent[];
    const moveEvent = assigns.find(a => a.varName === 'WS-STR');
    assert(moveEvent !== undefined, 'should have assign event for WS-STR');
    assertEqual(moveEvent!.sourceInfo?.conversionApplied, 'numeric-to-alphanumeric', 'conversion type');
  });
});

describe('Arithmetic Operations', () => {
  it('should ADD correctly', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-A', pic: '9(5)V99', value: 100.50, children: [] },
        { nodeType: 'data-item', level: 1, name: 'WS-B', pic: '9(5)V99', value: 200.25, children: [] },
      ],
      [{ stmtType: 'add', values: [{ exprType: 'variable', name: 'WS-B' }], to: 'WS-A', rounded: false }]
    );
    const tracer = new ExecutionTracer();
    const result = new CobolInterpreter(tracer).execute(prog);
    const val = result.variables.get('WS-A');
    assertApprox(decimalToNumber(val as any), 300.75, 0.01, 'sum');
  });

  it('should COMPUTE with ROUNDED', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-RESULT', pic: '9(5)V99', value: 0, children: [] },
      ],
      [{
        stmtType: 'compute', target: 'WS-RESULT', rounded: true,
        expression: {
          exprType: 'binary', op: '/',
          left: { exprType: 'literal', value: 10 },
          right: { exprType: 'literal', value: 3 },
        },
      }]
    );
    const tracer = new ExecutionTracer();
    const result = new CobolInterpreter(tracer).execute(prog);
    const val = result.variables.get('WS-RESULT');
    // 10/3 = 3.333... → ROUNDED to V99 = 3.33
    assertApprox(decimalToNumber(val as any), 3.33, 0.01, 'rounded result');
  });

  it('should record rounding detail in trace', () => {
    const prog = makeSimpleProgram(
      [{ nodeType: 'data-item', level: 1, name: 'WS-R', pic: '9(3)V99', value: 0, children: [] }],
      [{
        stmtType: 'compute', target: 'WS-R', rounded: true,
        expression: {
          exprType: 'binary', op: '/',
          left: { exprType: 'literal', value: 10 },
          right: { exprType: 'literal', value: 6 },
        },
      }]
    );
    const tracer = new ExecutionTracer();
    new CobolInterpreter(tracer).execute(prog);
    const arithEvents = tracer.getEvents().filter(e => e.eventType === 'arithmetic') as ArithmeticEvent[];
    assert(arithEvents.length > 0, 'should have arithmetic event');
    assert(arithEvents[0].rounded === true, 'should be marked rounded');
    // 10/6 = 1.6666... → ROUNDED V99 = 1.67, TRUNCATED = 1.66 → rounding detail should exist
    assert(arithEvents[0].roundingDetail !== undefined, 'should have rounding detail');
  });
});

describe('IF Statement', () => {
  it('should take THEN branch when condition is true', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-A', pic: '9(3)', value: 100, children: [] },
        { nodeType: 'data-item', level: 1, name: 'WS-RESULT', pic: 'X(5)', value: '', children: [] },
      ],
      [{
        stmtType: 'if',
        condition: { condType: 'comparison', op: '>', left: { exprType: 'variable', name: 'WS-A' }, right: { exprType: 'literal', value: 50 } },
        thenBlock: [{ stmtType: 'move', from: { exprType: 'literal', value: 'HIGH' }, to: 'WS-RESULT' }],
        elseBlock: [{ stmtType: 'move', from: { exprType: 'literal', value: 'LOW' }, to: 'WS-RESULT' }],
      }]
    );
    const tracer = new ExecutionTracer();
    const result = new CobolInterpreter(tracer).execute(prog);
    const val = result.variables.get('WS-RESULT');
    assert(val !== undefined && val.kind === 'alphanumeric', 'should be alphanumeric');
    assertEqual((val as any).bytes.trimEnd(), 'HIGH', 'then branch taken');
  });

  it('should record branch decision in trace', () => {
    const prog = makeSimpleProgram(
      [{ nodeType: 'data-item', level: 1, name: 'WS-A', pic: '9(3)', value: 10, children: [] }],
      [{
        stmtType: 'if',
        condition: { condType: 'comparison', op: '>', left: { exprType: 'variable', name: 'WS-A' }, right: { exprType: 'literal', value: 50 } },
        thenBlock: [],
        elseBlock: [],
      }]
    );
    const tracer = new ExecutionTracer();
    new CobolInterpreter(tracer).execute(prog);
    const branches = tracer.getEvents().filter(e => e.eventType === 'branch') as BranchEvent[];
    assert(branches.length === 1, 'should have 1 branch event');
    assertEqual(branches[0].branchTaken, 'else', 'should take else branch');
    assertEqual(branches[0].evaluatedTo, false, 'condition should be false');
  });
});

describe('PERFORM VARYING', () => {
  it('should loop correct number of times', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-I', pic: '9(3)', value: 0, children: [] },
        { nodeType: 'data-item', level: 1, name: 'WS-SUM', pic: '9(5)', value: 0, children: [] },
      ],
      [{
        stmtType: 'perform-varying',
        paragraphName: 'ADD-LOOP',
        variable: 'WS-I',
        from: { exprType: 'literal', value: 1 },
        by: { exprType: 'literal', value: 1 },
        until: { condType: 'comparison', op: '>', left: { exprType: 'variable', name: 'WS-I' }, right: { exprType: 'literal', value: 5 } },
      }],
      [{
        name: 'ADD-LOOP',
        statements: [
          { stmtType: 'add', values: [{ exprType: 'variable', name: 'WS-I' }], to: 'WS-SUM', rounded: false },
        ],
      }]
    );
    const tracer = new ExecutionTracer();
    const result = new CobolInterpreter(tracer).execute(prog);
    const sum = result.variables.get('WS-SUM');
    // 1 + 2 + 3 + 4 + 5 = 15
    assertApprox(decimalToNumber(sum as any), 15, 0.01, 'loop sum');

    // トレースにループイテレーションが5回記録されていること
    const loopEvents = tracer.getEvents().filter(e => e.eventType === 'loop-iteration');
    assertEqual(loopEvents.length, 5, 'loop iteration count');
  });
});

// ============================================================
// 3. トレース収集のテスト
// ============================================================

describe('Trace Collection', () => {
  it('should record program start and end', () => {
    const prog = makeSimpleProgram([], [{ stmtType: 'stop-run' }]);
    const tracer = new ExecutionTracer();
    new CobolInterpreter(tracer).execute(prog);
    const events = tracer.getEvents();
    assertEqual(events[0].eventType, 'program-start', 'first event');
    assertEqual(events[events.length - 1].eventType, 'program-end', 'last event');
  });

  it('should record variable initializations', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-A', pic: '9(3)', value: 42, children: [] },
        { nodeType: 'data-item', level: 1, name: 'WS-B', pic: 'X(5)', value: 'TEST', children: [] },
      ],
      [{ stmtType: 'stop-run' }]
    );
    const tracer = new ExecutionTracer();
    new CobolInterpreter(tracer).execute(prog);
    const inits = tracer.getEvents().filter(e => e.eventType === 'var-init') as VarInitEvent[];
    assertEqual(inits.length, 2, 'should have 2 init events');
    assertEqual(inits[0].varName, 'WS-A', 'first var');
    assertEqual(inits[0].cobolType, 'fixed-decimal', 'first type');
    assertEqual(inits[1].varName, 'WS-B', 'second var');
    assertEqual(inits[1].cobolType, 'alphanumeric', 'second type');
  });

  it('should generate correct summary', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-A', pic: '9(5)', value: 10, children: [] },
        { nodeType: 'data-item', level: 1, name: 'WS-B', pic: '9(5)', value: 20, children: [] },
      ],
      [
        { stmtType: 'add', values: [{ exprType: 'variable', name: 'WS-B' }], to: 'WS-A', rounded: false },
        {
          stmtType: 'if',
          condition: { condType: 'comparison', op: '>', left: { exprType: 'variable', name: 'WS-A' }, right: { exprType: 'literal', value: 25 } },
          thenBlock: [],
          elseBlock: [],
        },
        { stmtType: 'stop-run' },
      ]
    );
    const tracer = new ExecutionTracer();
    new CobolInterpreter(tracer).execute(prog);
    const summary = tracer.getSummary();

    assertEqual(summary.variableCount, 2, 'variable count');
    assert(summary.arithmeticCount >= 1, `arithmetic count should be >= 1, got ${summary.arithmeticCount}`);
    assertEqual(summary.branchCount, 1, 'branch count');
  });
});

// ============================================================
// 4. 統合テスト - ローン計算
// ============================================================

describe('Integration: Loan Calculator', () => {
  it('should compute monthly rate correctly', () => {
    const prog = makeSimpleProgram(
      [
        { nodeType: 'data-item', level: 1, name: 'WS-ANNUAL-RATE', pic: '9(2)V9(4)', value: 3.5, children: [] },
        { nodeType: 'data-item', level: 1, name: 'WS-MONTHLY-RATE', pic: '9(2)V9(6)', children: [] },
      ],
      [{ stmtType: 'perform', paragraphName: 'CALC-RATE' }],
      [{
        name: 'CALC-RATE',
        statements: [{
          stmtType: 'compute', target: 'WS-MONTHLY-RATE', rounded: true,
          expression: {
            exprType: 'binary', op: '/',
            left: {
              exprType: 'binary', op: '/',
              left: { exprType: 'variable', name: 'WS-ANNUAL-RATE' },
              right: { exprType: 'literal', value: 100 },
            },
            right: { exprType: 'literal', value: 12 },
          },
        }],
      }]
    );
    const tracer = new ExecutionTracer();
    const result = new CobolInterpreter(tracer).execute(prog);
    const rate = result.variables.get('WS-MONTHLY-RATE');
    // 3.5 / 100 / 12 = 0.002916...
    assertApprox(decimalToNumber(rate as any), 0.002917, 0.001, 'monthly rate');
  });
});

// ============================================================
// 結果出力
// ============================================================

console.log('\n══════════════════════════════════════════════');
console.log('  COBOL Instrumented Interpreter - Test Suite');
console.log('══════════════════════════════════════════════');

// テスト実行（describeブロックは定義時に実行される）

console.log('\n══════════════════════════════════════════════');
console.log(`  Results: ${passedTests}/${totalTests} passed, ${failedTests} failed`);
if (failedTests > 0) {
  console.log('\n  Failures:');
  for (const f of failures) {
    console.log(`    ❌ ${f}`);
  }
}
console.log('══════════════════════════════════════════════');
process.exit(failedTests > 0 ? 1 : 0);
