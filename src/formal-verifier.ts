/**
 * Formal Verifier - Lean仲介による統一的形式検証パイプライン
 *
 * 既存のランタイム検証と、新しいLean形式証明を統合する。
 * 「証明のCarrying」を統一的に扱う体系:
 *
 *   COBOL AST
 *     ├─→ Runtime Verification (既存: 実行トレースベース)
 *     │     └─→ VerificationReport
 *     ├─→ Lean IR Generation (新規: 表示的意味論)
 *     │     └─→ LeanFormalization
 *     └─→ Lean Proof Generation (新規: 定理と証明)
 *           └─→ ProofGenerationResult
 *
 *   ↓ 統合
 *
 *   Formal Proof Certificate
 *     ├─ Runtime verification results (concrete)
 *     ├─ Lean theorems with proofs (formal)
 *     ├─ Transformation correctness proof (bisimulation)
 *     └─ Unified confidence level
 *
 * 証明の強度:
 *   Runtime-only < Runtime+Formal(partial) < Runtime+Formal(full) < Lean-verified
 */

import { CobolProgram } from './ast';
import { ExecutionTracer } from './tracer';
import { CobolInterpreter, ExecutionResult } from './interpreter';
import { PropertySet } from './properties';
import { PropertyVerifier, VerificationReport } from './verifier';
import {
  LeanIRGenerator, LeanFormalization,
} from './lean-ir';
import {
  LeanProofGenerator, ProofGenerationResult,
  LeanTheorem, ProofLevel, ProofStats,
} from './lean-proof-generator';
import { formatCobolValue, CobolValue } from './types';

// ============================================================
// 統合的証明書の型
// ============================================================

/** 統合的証明の強度 */
export type FormalConfidenceLevel =
  | 'runtime-only'        // ランタイム検証のみ（既存）
  | 'runtime-with-sketch'  // ランタイム + 証明スケッチ
  | 'partially-formal'     // ランタイム + 一部Lean証明
  | 'formally-verified';   // 完全なLean証明

/** 統合的形式証明書 */
export interface FormalProofCertificate {
  /** 証明書ID */
  readonly certificateId: string;
  /** 生成日時 */
  readonly issuedAt: string;
  /** プログラムID */
  readonly programId: string;

  /** 統合的信頼性レベル */
  readonly confidenceLevel: FormalConfidenceLevel;

  /** ランタイム検証結果（既存） */
  readonly runtimeVerification: VerificationReport;

  /** Lean形式仕様 */
  readonly leanFormalization: LeanFormalization;

  /** Lean証明生成結果 */
  readonly formalProofs: ProofGenerationResult;

  /** プロパティごとの統合検証結果 */
  readonly unifiedResults: readonly UnifiedPropertyResult[];

  /** 変換正当性の要約 */
  readonly transformationSummary: TransformationSummary;

  /** 全体サマリー */
  readonly summary: FormalCertificateSummary;
}

/** プロパティごとの統合検証結果 */
export interface UnifiedPropertyResult {
  readonly propertyId: string;
  readonly description: string;
  /** ランタイム検証のステータス */
  readonly runtimeStatus: 'passed' | 'failed' | 'skipped';
  /** Lean証明のステータス */
  readonly formalStatus: 'proven' | 'sketch' | 'axiom' | 'not-formalized';
  /** 証明の強度レベル */
  readonly proofLevel: ProofLevel;
  /** 統合判定 */
  readonly unified: 'verified' | 'partially-verified' | 'unverified';
  /** Lean定理名 */
  readonly leanTheoremName: string;
  /** 使用されたwitness数 */
  readonly witnessCount: number;
}

/** 変換正当性の要約 */
export interface TransformationSummary {
  readonly sourceLang: string;
  readonly targetLang: string;
  readonly equivalenceStatus: 'proven' | 'sketch' | 'not-proven';
  readonly preservedProperties: number;
  readonly totalProperties: number;
  readonly bisimulationComponents: readonly string[];
}

/** 全体サマリー */
export interface FormalCertificateSummary {
  readonly totalProperties: number;
  readonly runtimePassed: number;
  readonly formallyProven: number;
  readonly partiallyVerified: number;
  readonly unverified: number;
  readonly proofStats: ProofStats;
  readonly leanLines: number;
  readonly witnessCount: number;
}

// ============================================================
// 統合検証パイプライン
// ============================================================

export class FormalVerificationPipeline {
  private program: CobolProgram;
  private propertySet: PropertySet;

  constructor(program: CobolProgram, propertySet: PropertySet) {
    this.program = program;
    this.propertySet = propertySet;
  }

  /**
   * 統合的形式検証を実行する
   *
   * Phase 1: ランタイム検証（既存）
   * Phase 2: Lean形式仕様の生成
   * Phase 3: Lean定理と証明の生成
   * Phase 4: 統合的証明書の構築
   */
  execute(): FormalVerificationExecution {
    const phases: PhaseResult[] = [];

    // === Phase 1: Runtime Verification ===
    const phase1Start = Date.now();
    const { result, tracer } = this.executeProgram();
    const verifier = new PropertyVerifier(
      tracer.getEvents(), result.variables, result.displayOutput
    );
    const runtimeReport = verifier.verify(this.propertySet);
    phases.push({
      name: 'Runtime Verification',
      duration: Date.now() - phase1Start,
      status: runtimeReport.allPassed ? 'success' : 'partial',
      details: `${runtimeReport.summary.passed}/${runtimeReport.summary.total} passed`,
    });

    // === Phase 2: Lean Formalization ===
    const phase2Start = Date.now();
    const leanGenerator = new LeanIRGenerator(this.program);
    const formalization = leanGenerator.generate();
    phases.push({
      name: 'Lean IR Generation',
      duration: Date.now() - phase2Start,
      status: 'success',
      details: `${formalization.stats.totalLeanLines} lines, ${formalization.stats.totalFunctions} functions`,
    });

    // === Phase 3: Lean Proof Generation ===
    const phase3Start = Date.now();
    const proofGenerator = new LeanProofGenerator(
      formalization, this.propertySet,
      tracer.getEvents(), result.variables
    );
    const proofResult = proofGenerator.generateProofs();
    phases.push({
      name: 'Lean Proof Generation',
      duration: Date.now() - phase3Start,
      status: proofResult.stats.formalProofCoverage >= 0.8 ? 'success' : 'partial',
      details: `${proofResult.stats.totalTheorems} theorems, ${(proofResult.stats.formalProofCoverage * 100).toFixed(0)}% formal coverage`,
    });

    // === Phase 4: Unified Certificate ===
    const phase4Start = Date.now();
    const certificate = this.buildUnifiedCertificate(
      runtimeReport, formalization, proofResult
    );
    phases.push({
      name: 'Unified Certificate',
      duration: Date.now() - phase4Start,
      status: 'success',
      details: `Confidence: ${certificate.confidenceLevel}`,
    });

    return {
      certificate,
      phases,
      executionResult: result,
      traceSummary: tracer.getSummary(),
    };
  }

  // ============================================================
  // 統合的証明書の構築
  // ============================================================

  private buildUnifiedCertificate(
    runtimeReport: VerificationReport,
    formalization: LeanFormalization,
    proofResult: ProofGenerationResult
  ): FormalProofCertificate {
    // 各プロパティの統合結果
    const unifiedResults = this.buildUnifiedResults(runtimeReport, proofResult);

    // 変換正当性の要約
    const transformationSummary = this.buildTransformationSummary(proofResult);

    // 全体サマリー
    const summary = this.buildSummary(unifiedResults, proofResult, formalization);

    // 信頼性レベルの決定
    const confidenceLevel = this.determineConfidenceLevel(unifiedResults, proofResult);

    return {
      certificateId: `formal-cert-${this.program.programId}-${Date.now()}`,
      issuedAt: new Date().toISOString(),
      programId: this.program.programId,
      confidenceLevel,
      runtimeVerification: runtimeReport,
      leanFormalization: formalization,
      formalProofs: proofResult,
      unifiedResults,
      transformationSummary,
      summary,
    };
  }

  private buildUnifiedResults(
    runtimeReport: VerificationReport,
    proofResult: ProofGenerationResult
  ): UnifiedPropertyResult[] {
    const results: UnifiedPropertyResult[] = [];

    for (const prop of this.propertySet.properties) {
      const runtimeResult = runtimeReport.results.find(r => r.propertyId === prop.id);
      const theorem = proofResult.theorems.find(t => t.propertyId === prop.id);

      const runtimeStatus = runtimeResult?.status ?? 'skipped';
      const formalStatus = this.classifyFormalStatus(theorem);
      const proofLevel = theorem?.proofLevel ?? 'axiom';
      const unified = this.classifyUnified(runtimeStatus, formalStatus);

      results.push({
        propertyId: prop.id,
        description: prop.description,
        runtimeStatus,
        formalStatus,
        proofLevel,
        unified,
        leanTheoremName: theorem?.theoremName ?? '(none)',
        witnessCount: theorem?.witnesses.length ?? 0,
      });
    }

    return results;
  }

  private classifyFormalStatus(theorem?: LeanTheorem): UnifiedPropertyResult['formalStatus'] {
    if (!theorem) return 'not-formalized';
    if (theorem.kind === 'axiom') return 'axiom';
    if (theorem.strategy === 'sorry') return 'sketch';
    return 'proven';
  }

  private classifyUnified(
    runtimeStatus: string,
    formalStatus: UnifiedPropertyResult['formalStatus']
  ): UnifiedPropertyResult['unified'] {
    if (runtimeStatus === 'passed' && formalStatus === 'proven') return 'verified';
    if (runtimeStatus === 'passed' || formalStatus === 'proven') return 'partially-verified';
    return 'unverified';
  }

  private buildTransformationSummary(proofResult: ProofGenerationResult): TransformationSummary {
    const transProof = proofResult.transformationProof;
    return {
      sourceLang: transProof.sourceLang,
      targetLang: transProof.targetLang,
      equivalenceStatus: transProof.equivalenceTheorem.strategy === 'sorry' ? 'sketch' : 'proven',
      preservedProperties: transProof.preservationTheorems.length,
      totalProperties: this.propertySet.properties.length,
      bisimulationComponents: transProof.equivalenceTheorem.dependencies,
    };
  }

  private buildSummary(
    unified: UnifiedPropertyResult[],
    proofResult: ProofGenerationResult,
    formalization: LeanFormalization
  ): FormalCertificateSummary {
    return {
      totalProperties: unified.length,
      runtimePassed: unified.filter(r => r.runtimeStatus === 'passed').length,
      formallyProven: unified.filter(r => r.formalStatus === 'proven').length,
      partiallyVerified: unified.filter(r => r.unified === 'partially-verified').length,
      unverified: unified.filter(r => r.unified === 'unverified').length,
      proofStats: proofResult.stats,
      leanLines: formalization.stats.totalLeanLines + proofResult.leanProofSource.split('\n').length,
      witnessCount: proofResult.stats.totalWitnesses,
    };
  }

  private determineConfidenceLevel(
    unified: UnifiedPropertyResult[],
    proofResult: ProofGenerationResult
  ): FormalConfidenceLevel {
    const allFormal = unified.every(r => r.formalStatus === 'proven');
    const someFormal = unified.some(r => r.formalStatus === 'proven');
    const allRuntime = unified.every(r => r.runtimeStatus === 'passed');

    if (allFormal && allRuntime) return 'formally-verified';
    if (someFormal && allRuntime) return 'partially-formal';
    if (allRuntime) return 'runtime-with-sketch';
    return 'runtime-only';
  }

  // ============================================================
  // ヘルパー
  // ============================================================

  private executeProgram(): { result: ExecutionResult; tracer: ExecutionTracer } {
    const tracer = new ExecutionTracer();
    const interpreter = new CobolInterpreter(tracer);
    const result = interpreter.execute(this.program);
    return { result, tracer };
  }
}

// ============================================================
// 実行結果の型
// ============================================================

export interface PhaseResult {
  readonly name: string;
  readonly duration: number;
  readonly status: 'success' | 'partial' | 'failed';
  readonly details: string;
}

export interface FormalVerificationExecution {
  readonly certificate: FormalProofCertificate;
  readonly phases: readonly PhaseResult[];
  readonly executionResult: ExecutionResult;
  readonly traceSummary: import('./tracer').TraceSummary;
}

// ============================================================
// フォーマッター
// ============================================================

export function formatFormalCertificate(cert: FormalProofCertificate): string {
  const lines: string[] = [];

  lines.push('');
  lines.push('╔═══════════════════════════════════════════════════════════════════════╗');
  lines.push('║  FORMAL PROOF CERTIFICATE - Lean-Mediated Verification               ║');
  lines.push('╠═══════════════════════════════════════════════════════════════════════╣');
  lines.push('');
  lines.push(`  Certificate ID:    ${cert.certificateId}`);
  lines.push(`  Program:           ${cert.programId}`);
  lines.push(`  Issued At:         ${cert.issuedAt}`);
  lines.push(`  Confidence Level:  ${cert.confidenceLevel.toUpperCase()}`);
  lines.push('');

  // Unified Results
  lines.push('--- Unified Property Verification ---');
  lines.push('');
  lines.push('  Property              Runtime   Formal         Level        Unified');
  lines.push('  ────────────────────  ────────  ─────────────  ───────────  ──────────────');
  for (const r of cert.unifiedResults) {
    const runtime = r.runtimeStatus.padEnd(8);
    const formal = r.formalStatus.padEnd(13);
    const level = r.proofLevel.padEnd(11);
    const unified = r.unified;
    lines.push(`  ${r.propertyId.padEnd(22)} ${runtime}  ${formal}  ${level}  ${unified}`);
  }
  lines.push('');

  // Lean Formalization Stats
  lines.push('--- Lean 4 Formalization ---');
  lines.push('');
  lines.push(`  State fields:      ${cert.leanFormalization.stats.totalFields}`);
  lines.push(`  Semantic functions: ${cert.leanFormalization.stats.totalFunctions}`);
  lines.push(`  Type constraints:  ${cert.leanFormalization.stats.totalConstraints}`);
  lines.push(`  Total Lean lines:  ${cert.summary.leanLines}`);
  lines.push('');

  // Proof Stats
  lines.push('--- Proof Statistics ---');
  lines.push('');
  lines.push(`  Total theorems:    ${cert.summary.proofStats.totalTheorems}`);
  lines.push(`  By level:`);
  for (const [level, count] of Object.entries(cert.summary.proofStats.byLevel)) {
    if (count > 0) {
      lines.push(`    ${level.padEnd(12)} ${count}`);
    }
  }
  lines.push(`  By strategy:`);
  for (const [strategy, count] of Object.entries(cert.summary.proofStats.byStrategy)) {
    if (count > 0) {
      lines.push(`    ${strategy.padEnd(20)} ${count}`);
    }
  }
  lines.push(`  Runtime witnesses: ${cert.summary.witnessCount}`);
  lines.push(`  Formal coverage:   ${(cert.summary.proofStats.formalProofCoverage * 100).toFixed(1)}%`);
  lines.push('');

  // Transformation
  lines.push('--- Transformation Correctness ---');
  lines.push('');
  lines.push(`  Source:             ${cert.transformationSummary.sourceLang}`);
  lines.push(`  Target:             ${cert.transformationSummary.targetLang}`);
  lines.push(`  Equivalence:        ${cert.transformationSummary.equivalenceStatus}`);
  lines.push(`  Preserved:          ${cert.transformationSummary.preservedProperties}/${cert.transformationSummary.totalProperties} properties`);
  lines.push(`  Bisimulation via:   ${cert.transformationSummary.bisimulationComponents.join(', ')}`);
  lines.push('');

  // Summary
  lines.push('--- Summary ---');
  lines.push('');
  lines.push(`  Total Properties:       ${cert.summary.totalProperties}`);
  lines.push(`  Runtime Passed:         ${cert.summary.runtimePassed}`);
  lines.push(`  Formally Proven:        ${cert.summary.formallyProven}`);
  lines.push(`  Partially Verified:     ${cert.summary.partiallyVerified}`);
  lines.push(`  Unverified:             ${cert.summary.unverified}`);
  lines.push('');
  lines.push(`  ┌──────────────────────────────────────────────────────────────┐`);
  lines.push(`  │  Confidence: ${cert.confidenceLevel.toUpperCase().padEnd(48)}│`);
  lines.push(`  │                                                              │`);
  lines.push(`  │  Proof-Carrying Chain:                                       │`);
  lines.push(`  │  COBOL ──[Lean IR]──> Formal Spec                           │`);
  lines.push(`  │    │                     │                                   │`);
  lines.push(`  │    │                     ├─ Property Theorems (${String(cert.summary.proofStats.totalTheorems).padStart(2)})           │`);
  lines.push(`  │    │                     ├─ Type Constraints (${String(cert.leanFormalization.stats.totalConstraints).padStart(2)})           │`);
  lines.push(`  │    │                     └─ Bisimulation Proof               │`);
  lines.push(`  │    │                                                         │`);
  lines.push(`  │    └──[CodeGen]──> TypeScript                                │`);
  lines.push(`  │                     │                                        │`);
  lines.push(`  │                     └─ Preservation Theorems (${String(cert.transformationSummary.preservedProperties).padStart(2)})          │`);
  lines.push(`  │                                                              │`);
  lines.push(`  │  Runtime + Formal = Unified Proof Certificate                │`);
  lines.push(`  └──────────────────────────────────────────────────────────────┘`);
  lines.push('');
  lines.push('╚═══════════════════════════════════════════════════════════════════════╝');

  return lines.join('\n');
}

export function formatPhaseResults(phases: readonly PhaseResult[]): string {
  const lines: string[] = [];
  lines.push('');
  lines.push('--- Pipeline Execution ---');
  lines.push('');
  for (const phase of phases) {
    const icon = phase.status === 'success' ? '[OK]' : phase.status === 'partial' ? '[!!]' : '[NG]';
    lines.push(`  ${icon} ${phase.name.padEnd(30)} ${phase.duration}ms  ${phase.details}`);
  }
  lines.push('');
  return lines.join('\n');
}
