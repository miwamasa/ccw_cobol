/**
 * Code Generator - 実行トレースからTypeScriptコードを生成
 * 
 * このPOCでは、トレース情報を活用して以下を実証する:
 * 1. 変数の実際の使われ方から最適な型を推論
 * 2. 分岐の実行パターンからコードの意図を推定
 * 3. 算術演算の精度要件を特定
 * 4. 実行されたパスのみにフォーカスしたコード生成
 * 
 * 実プロダクトではLLMがこの情報を受け取ってコード生成するが、
 * POCではルールベースでTypeScript生成を実証する。
 */

import { CobolProgram, Statement, Expression, Condition, DataItemDef } from './ast';
import { TraceSummary, TraceEvent, VarInitEvent, ArithmeticEvent, BranchEvent } from './tracer';

export interface GeneratedCode {
  typescript: string;
  insights: string[];  // 生成時に発見した知見
}

export function generateTypeScript(
  program: CobolProgram,
  events: readonly TraceEvent[],
  summary: TraceSummary
): GeneratedCode {
  const insights: string[] = [];
  const lines: string[] = [];

  lines.push('/**');
  lines.push(` * Auto-generated from COBOL program: ${program.programId}`);
  lines.push(` * Generated via Instrumented Interpreter trace analysis`);
  lines.push(` * Trace statistics: ${summary.totalStatements} statements, ${summary.totalEvents} events`);
  lines.push(' */');
  lines.push('');

  // --- Insight 1: 変数の型推論 ---
  lines.push('// ============================================================');
  lines.push('// Type Definitions (inferred from execution traces)');
  lines.push('// ============================================================');
  lines.push('');

  const varInits = events.filter(e => e.eventType === 'var-init') as VarInitEvent[];
  const arithmeticEvents = events.filter(e => e.eventType === 'arithmetic') as ArithmeticEvent[];

  // 変数が算術演算に使われたかどうかで型を決定
  const arithmeticVars = new Set<string>();
  for (const ae of arithmeticEvents) {
    arithmeticVars.add(ae.targetVar);
    for (const op of ae.operands) {
      if (!op.name.startsWith('"') && !op.name.startsWith('(')) {
        arithmeticVars.add(op.name);
      }
    }
  }

  // 精度要件の検出
  const precisionRequirements = new Map<string, { scale: number; needsRounding: boolean }>();
  for (const ae of arithmeticEvents) {
    if (ae.roundingDetail) {
      insights.push(
        `⚠️ Variable "${ae.targetVar}" requires rounding (${ae.roundingDetail.truncatedDigits} decimal places). ` +
        `Use BigDecimal or fixed-point library in production.`
      );
      precisionRequirements.set(ae.targetVar, {
        scale: ae.roundingDetail.truncatedDigits,
        needsRounding: ae.rounded,
      });
    }
  }

  // Interface生成
  const needsBigDecimal = precisionRequirements.size > 0;
  if (needsBigDecimal) {
    lines.push('// ⚠️ PRECISION WARNING: This program uses fixed-point arithmetic.');
    lines.push('// For production use, replace `number` with a BigDecimal library.');
    lines.push('import { BigDecimal } from "bigdecimal"; // recommended for production');
    lines.push('');
    insights.push('🔢 Program uses fixed-point arithmetic with rounding. BigDecimal recommended for production.');
  }

  lines.push('interface ProgramState {');
  for (const vi of varInits) {
    const isArithmetic = arithmeticVars.has(vi.varName);
    const tsType = vi.cobolType === 'fixed-decimal' ? 'number' : 'string';
    const comment = isArithmetic ? ' // used in arithmetic operations' : '';
    const precReq = precisionRequirements.get(vi.varName);
    const precComment = precReq
      ? ` // PRECISION: ${precReq.scale} decimal places, ${precReq.needsRounding ? 'ROUNDED' : 'TRUNCATED'}`
      : '';
    lines.push(`  ${camelCase(vi.varName)}: ${tsType};${comment}${precComment}`);
  }
  lines.push('}');
  lines.push('');

  // --- Insight 2: 初期値 ---
  lines.push('function createInitialState(): ProgramState {');
  lines.push('  return {');
  for (const vi of varInits) {
    const val = vi.cobolType === 'fixed-decimal'
      ? vi.initialValue
      : `"${vi.initialValue.replace(/"/g, '\\"')}"`;
    lines.push(`    ${camelCase(vi.varName)}: ${val},`);
  }
  lines.push('  };');
  lines.push('}');
  lines.push('');

  // --- Insight 3: パラグラフ → 関数 ---
  lines.push('// ============================================================');
  lines.push('// Functions (from COBOL paragraphs)');
  lines.push('// ============================================================');
  lines.push('');

  // パラグラフの呼び出し関係を分析
  for (const [paraName, callCount] of Object.entries(summary.paragraphCalls)) {
    insights.push(`📊 Paragraph "${paraName}" was called ${callCount} time(s) during trace execution.`);
  }

  // パラグラフのコード生成
  for (const para of program.paragraphs) {
    const callCount = summary.paragraphCalls[para.name] || 0;
    lines.push(`/** Paragraph: ${para.name} (called ${callCount}x in trace) */`);
    lines.push(`function ${camelCase(para.name)}(state: ProgramState): void {`);
    for (const stmt of para.statements) {
      const stmtLines = generateStatement(stmt, '  ');
      lines.push(...stmtLines);
    }
    lines.push('}');
    lines.push('');
  }

  // --- Insight 4: メイン関数 ---
  lines.push('// ============================================================');
  lines.push('// Main execution');
  lines.push('// ============================================================');
  lines.push('');
  lines.push('function main(): ProgramState {');
  lines.push('  const state = createInitialState();');
  for (const stmt of program.mainStatements) {
    const stmtLines = generateStatement(stmt, '  ');
    lines.push(...stmtLines);
  }
  lines.push('  return state;');
  lines.push('}');
  lines.push('');

  // --- Insight 5: 分岐カバレッジ分析 ---
  lines.push('// ============================================================');
  lines.push('// Branch Coverage Analysis (from trace)');
  lines.push('// ============================================================');
  for (const [cond, coverage] of Object.entries(summary.branchCoverage)) {
    const total = coverage.then + coverage.else;
    const coveredBoth = coverage.then > 0 && coverage.else > 0;
    lines.push(`// Condition: ${cond}`);
    lines.push(`//   THEN branch: ${coverage.then}/${total} (${pct(coverage.then, total)})`);
    lines.push(`//   ELSE branch: ${coverage.else}/${total} (${pct(coverage.else, total)})`);
    if (!coveredBoth) {
      lines.push(`//   ⚠️ WARNING: Only ${coverage.then > 0 ? 'THEN' : 'ELSE'} branch was exercised!`);
      insights.push(
        `⚠️ Branch "${cond}" only exercised ${coverage.then > 0 ? 'THEN' : 'ELSE'} path. ` +
        `Need additional test data to cover the other branch.`
      );
    }
  }
  lines.push('');

  // --- Insight 6: 型変換の検出 ---
  if (Object.keys(summary.typeTransitions).length > 0) {
    lines.push('// ============================================================');
    lines.push('// Type Conversion Warnings (from trace)');
    lines.push('// ============================================================');
    for (const [varName, transitions] of Object.entries(summary.typeTransitions)) {
      for (const t of transitions) {
        lines.push(`// ${varName}: ${t}`);
        insights.push(`🔄 Implicit type conversion detected for "${varName}": ${t}`);
      }
    }
  }

  lines.push('');
  lines.push('// Run');
  lines.push('const result = main();');
  lines.push('console.log("Final state:", result);');

  return {
    typescript: lines.join('\n'),
    insights,
  };
}

// ============================================================
// 文のコード生成
// ============================================================

function generateStatement(stmt: Statement, indent: string): string[] {
  const lines: string[] = [];
  switch (stmt.stmtType) {
    case 'move':
      lines.push(`${indent}state.${camelCase(stmt.to)} = ${genExpr(stmt.from)};`);
      break;
    case 'add': {
      const target = camelCase(stmt.giving || stmt.to);
      const addExprs = stmt.values.map(v => genExpr(v)).join(' + ');
      if (stmt.giving) {
        lines.push(`${indent}state.${target} = ${addExprs};`);
      } else {
        lines.push(`${indent}state.${target} += ${addExprs};`);
      }
      break;
    }
    case 'subtract': {
      const target = camelCase(stmt.giving || stmt.from);
      const subExprs = stmt.values.map(v => genExpr(v)).join(' + ');
      if (stmt.giving) {
        lines.push(`${indent}state.${target} = state.${camelCase(stmt.from)} - (${subExprs});`);
      } else {
        lines.push(`${indent}state.${target} -= ${subExprs};`);
      }
      break;
    }
    case 'multiply': {
      const target = camelCase(stmt.giving || '');
      if (stmt.giving) {
        lines.push(`${indent}state.${target} = ${genExpr(stmt.value)} * ${genExpr(stmt.by)};`);
      } else {
        lines.push(`${indent}// MULTIPLY ${genExpr(stmt.value)} BY ${genExpr(stmt.by)}`);
      }
      break;
    }
    case 'divide': {
      const target = camelCase(stmt.giving || '');
      if (stmt.giving) {
        lines.push(`${indent}state.${target} = ${genExpr(stmt.value)} / ${genExpr(stmt.by)};`);
      }
      break;
    }
    case 'compute':
      lines.push(`${indent}state.${camelCase(stmt.target)} = ${genExpr(stmt.expression)};`);
      break;
    case 'if':
      lines.push(`${indent}if (${genCondition(stmt.condition)}) {`);
      for (const s of stmt.thenBlock) lines.push(...generateStatement(s, indent + '  '));
      if (stmt.elseBlock.length > 0) {
        lines.push(`${indent}} else {`);
        for (const s of stmt.elseBlock) lines.push(...generateStatement(s, indent + '  '));
      }
      lines.push(`${indent}}`);
      break;
    case 'perform':
      lines.push(`${indent}${camelCase(stmt.paragraphName)}(state);`);
      break;
    case 'perform-varying':
      lines.push(`${indent}for (state.${camelCase(stmt.variable)} = ${genExpr(stmt.from)}; !(${genCondition(stmt.until)}); state.${camelCase(stmt.variable)} += ${genExpr(stmt.by)}) {`);
      lines.push(`${indent}  ${camelCase(stmt.paragraphName)}(state);`);
      lines.push(`${indent}}`);
      break;
    case 'perform-times':
      lines.push(`${indent}for (let _i = 0; _i < ${genExpr(stmt.times)}; _i++) {`);
      lines.push(`${indent}  ${camelCase(stmt.paragraphName)}(state);`);
      lines.push(`${indent}}`);
      break;
    case 'display':
      lines.push(`${indent}console.log(${stmt.values.map(v => genExpr(v)).join(', ')});`);
      break;
    case 'stop-run':
      lines.push(`${indent}return state;`);
      break;
  }
  return lines;
}

function genExpr(expr: Expression): string {
  switch (expr.exprType) {
    case 'literal':
      return typeof expr.value === 'string' ? `"${expr.value}"` : expr.value.toString();
    case 'variable':
      return `state.${camelCase(expr.name)}`;
    case 'binary':
      const op = expr.op === '**' ? '**' : expr.op;
      return `(${genExpr(expr.left)} ${op} ${genExpr(expr.right)})`;
    case 'unary':
      return `(-${genExpr(expr.operand)})`;
  }
}

function genCondition(cond: Condition): string {
  switch (cond.condType) {
    case 'comparison': {
      const op = cond.op === '=' ? '===' : cond.op === '!=' ? '!==' : cond.op;
      return `${genExpr(cond.left)} ${op} ${genExpr(cond.right)}`;
    }
    case 'logical':
      return `(${genCondition(cond.left)} ${cond.op === 'AND' ? '&&' : '||'} ${genCondition(cond.right)})`;
    case 'not':
      return `!(${genCondition(cond.operand)})`;
  }
}

// ============================================================
// ユーティリティ
// ============================================================

function camelCase(s: string): string {
  return s.toLowerCase()
    .replace(/[-_]+(.)/g, (_, c: string) => c.toUpperCase())
    .replace(/^(.)/, (_, c: string) => c.toLowerCase());
}

function pct(n: number, total: number): string {
  return total === 0 ? '0%' : `${Math.round(n / total * 100)}%`;
}
