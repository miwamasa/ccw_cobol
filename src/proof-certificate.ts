/**
 * Proof Certificate - モダナイゼーションの証明書生成
 *
 * 元のCOBOLプログラムに対するプロパティ検証結果と、
 * モダナイゼーション後のコードに対する同一プロパティの検証結果を
 * 組み合わせて、変換の正当性を証明する「Proof Certificate」を生成する。
 *
 * Proof Certificate の構造:
 * 1. プロパティセット（何を保証するか）
 * 2. ソース検証結果（元のCOBOLで成立したか）
 * 3. ターゲット検証結果（変換後のコードで成立したか）
 * 4. クロス検証結果（ソースとターゲットの出力比較）
 * 5. 総合判定（全プロパティが保存されたか）
 */

import { PropertySet, Property } from './properties';
import { VerificationReport, PropertyVerificationResult } from './verifier';

// ============================================================
// Proof Certificate の型
// ============================================================

export type CertificateStatus = 'valid' | 'invalid' | 'partial';

export interface ProofCertificate {
  /** 証明書ID */
  readonly certificateId: string;
  /** 生成日時 */
  readonly issuedAt: string;
  /** 元プログラムID */
  readonly sourceProgramId: string;
  /** ターゲット言語 */
  readonly targetLanguage: string;

  /** 証明書の総合ステータス */
  readonly status: CertificateStatus;

  /** 検証に使われたプロパティセット */
  readonly propertySet: PropertySet;

  /** ソース（COBOL）側の検証結果 */
  readonly sourceVerification: VerificationReport;

  /** ターゲット（生成コード）側の検証結果 */
  readonly targetVerification: VerificationReport | null;

  /** クロス検証結果 */
  readonly crossVerification: CrossVerificationResult;

  /** 各プロパティの保存状態 */
  readonly propertyPreservation: readonly PropertyPreservationEntry[];

  /** 全体サマリー */
  readonly summary: CertificateSummary;
}

export interface PropertyPreservationEntry {
  readonly propertyId: string;
  readonly propertyType: Property['propertyType'];
  readonly description: string;
  /** ソース側のステータス */
  readonly sourceStatus: 'passed' | 'failed' | 'skipped';
  /** ターゲット側のステータス */
  readonly targetStatus: 'passed' | 'failed' | 'skipped' | 'not-verified';
  /** プロパティが保存されたか */
  readonly preserved: boolean;
  /** 保存に関する詳細メッセージ */
  readonly message: string;
}

export interface CrossVerificationResult {
  /** DISPLAY出力の比較 */
  readonly outputComparison: OutputComparisonResult;
  /** 最終変数状態の比較 */
  readonly stateComparison: StateComparisonResult;
}

export interface OutputComparisonResult {
  readonly status: 'match' | 'mismatch' | 'not-compared';
  readonly sourceLines: readonly string[];
  readonly targetLines: readonly string[];
  readonly mismatches: readonly OutputMismatch[];
}

export interface OutputMismatch {
  readonly lineIndex: number;
  readonly sourceLine: string;
  readonly targetLine: string;
  readonly detail: string;
}

export interface StateComparisonResult {
  readonly status: 'match' | 'mismatch' | 'not-compared';
  readonly comparisons: readonly StateVarComparison[];
}

export interface StateVarComparison {
  readonly varName: string;
  readonly sourceValue: string;
  readonly targetValue: string;
  readonly match: boolean;
  readonly tolerance: number;
}

export interface CertificateSummary {
  readonly totalProperties: number;
  readonly preservedProperties: number;
  readonly violatedProperties: number;
  readonly skippedProperties: number;
  /** 保存率 */
  readonly preservationRate: number;
  /** 出力一致か */
  readonly outputEquivalent: boolean;
  /** 状態一致か */
  readonly stateEquivalent: boolean;
}

// ============================================================
// Proof Certificate ビルダー
// ============================================================

export class ProofCertificateBuilder {
  private sourceProgramId: string;
  private targetLanguage: string;
  private propertySet: PropertySet;
  private sourceReport: VerificationReport;
  private targetReport: VerificationReport | null = null;
  private sourceOutput: string[] = [];
  private targetOutput: string[] = [];
  private sourceState: Map<string, string> = new Map();
  private targetState: Map<string, string> = new Map();
  private numericTolerance: number = 0.01;

  constructor(
    sourceProgramId: string,
    targetLanguage: string,
    propertySet: PropertySet,
    sourceReport: VerificationReport
  ) {
    this.sourceProgramId = sourceProgramId;
    this.targetLanguage = targetLanguage;
    this.propertySet = propertySet;
    this.sourceReport = sourceReport;
  }

  /** ターゲット側の検証結果を設定 */
  withTargetVerification(report: VerificationReport): this {
    this.targetReport = report;
    return this;
  }

  /** ソース出力を設定 */
  withSourceOutput(output: string[]): this {
    this.sourceOutput = output;
    return this;
  }

  /** ターゲット出力を設定 */
  withTargetOutput(output: string[]): this {
    this.targetOutput = output;
    return this;
  }

  /** ソースの最終変数状態を設定 */
  withSourceState(state: Map<string, string>): this {
    this.sourceState = state;
    return this;
  }

  /** ターゲットの最終変数状態を設定 */
  withTargetState(state: Map<string, string>): this {
    this.targetState = state;
    return this;
  }

  /** 数値比較の許容誤差を設定 */
  withNumericTolerance(tolerance: number): this {
    this.numericTolerance = tolerance;
    return this;
  }

  /** Proof Certificate を生成 */
  build(): ProofCertificate {
    const propertyPreservation = this.buildPreservationEntries();
    const crossVerification = this.buildCrossVerification();
    const summary = this.buildSummary(propertyPreservation, crossVerification);

    let status: CertificateStatus;
    if (summary.preservationRate === 1.0 && summary.outputEquivalent && summary.stateEquivalent) {
      status = 'valid';
    } else if (summary.preservedProperties > 0) {
      status = 'partial';
    } else {
      status = 'invalid';
    }

    return {
      certificateId: `cert-${this.sourceProgramId}-${Date.now()}`,
      issuedAt: new Date().toISOString(),
      sourceProgramId: this.sourceProgramId,
      targetLanguage: this.targetLanguage,
      status,
      propertySet: this.propertySet,
      sourceVerification: this.sourceReport,
      targetVerification: this.targetReport,
      crossVerification,
      propertyPreservation,
      summary,
    };
  }

  private buildPreservationEntries(): PropertyPreservationEntry[] {
    const entries: PropertyPreservationEntry[] = [];

    for (const prop of this.propertySet.properties) {
      const sourceResult = this.sourceReport.results.find(r => r.propertyId === prop.id);
      const targetResult = this.targetReport?.results.find(r => r.propertyId === prop.id);

      const sourceStatus = sourceResult?.status ?? 'skipped';
      const targetStatus = targetResult?.status ?? 'not-verified';

      // プロパティが「保存」されたかの判定ロジック:
      // - ソースで passed かつ ターゲットで passed → 保存された
      // - ソースで passed かつ ターゲットで failed → 保存されていない
      // - ソースで failed → ソースで成立しないので保存の議論はN/A
      // - ターゲットが未検証 → ソースの結果のみで仮判定
      let preserved: boolean;
      let message: string;

      if (sourceStatus === 'passed' && targetStatus === 'passed') {
        preserved = true;
        message = 'Property preserved: holds in both source and target';
      } else if (sourceStatus === 'passed' && targetStatus === 'failed') {
        preserved = false;
        message = 'Property NOT preserved: holds in source but violated in target';
      } else if (sourceStatus === 'passed' && targetStatus === 'not-verified') {
        preserved = true; // ソースでは成立、ターゲット未検証
        message = 'Property holds in source (target not yet verified)';
      } else if (sourceStatus === 'failed') {
        preserved = false;
        message = 'Property does not hold even in source';
      } else {
        preserved = true; // skipped
        message = 'Property was skipped (not applicable)';
      }

      entries.push({
        propertyId: prop.id,
        propertyType: prop.propertyType,
        description: prop.description,
        sourceStatus,
        targetStatus,
        preserved,
        message,
      });
    }

    return entries;
  }

  private buildCrossVerification(): CrossVerificationResult {
    return {
      outputComparison: this.compareOutputs(),
      stateComparison: this.compareStates(),
    };
  }

  private compareOutputs(): OutputComparisonResult {
    if (this.targetOutput.length === 0) {
      return {
        status: 'not-compared',
        sourceLines: this.sourceOutput,
        targetLines: [],
        mismatches: [],
      };
    }

    const mismatches: OutputMismatch[] = [];
    const maxLen = Math.max(this.sourceOutput.length, this.targetOutput.length);

    for (let i = 0; i < maxLen; i++) {
      const src = this.sourceOutput[i] ?? '';
      const tgt = this.targetOutput[i] ?? '';

      if (!this.outputLinesMatch(src, tgt)) {
        mismatches.push({
          lineIndex: i,
          sourceLine: src,
          targetLine: tgt,
          detail: i >= this.sourceOutput.length ? 'Extra line in target'
                : i >= this.targetOutput.length ? 'Missing line in target'
                : 'Content mismatch',
        });
      }
    }

    return {
      status: mismatches.length === 0 ? 'match' : 'mismatch',
      sourceLines: this.sourceOutput,
      targetLines: this.targetOutput,
      mismatches,
    };
  }

  private outputLinesMatch(src: string, tgt: string): boolean {
    if (src === tgt) return true;

    // 数値部分のみ許容誤差を考慮して比較
    const numRegex = /[-+]?\d+\.?\d*/g;
    const srcNums = src.match(numRegex) || [];
    const tgtNums = tgt.match(numRegex) || [];

    if (srcNums.length !== tgtNums.length) return false;

    // 数値以外の部分が一致するか
    const srcText = src.replace(numRegex, '###');
    const tgtText = tgt.replace(numRegex, '###');
    if (srcText !== tgtText) return false;

    // 数値部分を許容誤差で比較
    for (let i = 0; i < srcNums.length; i++) {
      const s = parseFloat(srcNums[i]);
      const t = parseFloat(tgtNums[i]);
      if (Math.abs(s - t) > this.numericTolerance) return false;
    }

    return true;
  }

  private compareStates(): StateComparisonResult {
    if (this.targetState.size === 0) {
      return { status: 'not-compared', comparisons: [] };
    }

    const comparisons: StateVarComparison[] = [];

    for (const [varName, sourceValue] of this.sourceState) {
      const targetValue = this.targetState.get(varName) ?? '';
      const srcNum = parseFloat(sourceValue);
      const tgtNum = parseFloat(targetValue);

      let match: boolean;
      if (!isNaN(srcNum) && !isNaN(tgtNum)) {
        match = Math.abs(srcNum - tgtNum) <= this.numericTolerance;
      } else {
        match = sourceValue.trim() === targetValue.trim();
      }

      comparisons.push({
        varName,
        sourceValue,
        targetValue,
        match,
        tolerance: this.numericTolerance,
      });
    }

    const allMatch = comparisons.every(c => c.match);
    return {
      status: allMatch ? 'match' : 'mismatch',
      comparisons,
    };
  }

  private buildSummary(
    entries: PropertyPreservationEntry[],
    cross: CrossVerificationResult
  ): CertificateSummary {
    const total = entries.length;
    const preserved = entries.filter(e => e.preserved).length;
    const violated = entries.filter(e => !e.preserved && e.sourceStatus !== 'skipped').length;
    const skipped = entries.filter(e => e.sourceStatus === 'skipped').length;

    const checkableCount = total - skipped;
    const preservationRate = checkableCount > 0 ? preserved / checkableCount : 1.0;

    return {
      totalProperties: total,
      preservedProperties: preserved,
      violatedProperties: violated,
      skippedProperties: skipped,
      preservationRate,
      outputEquivalent: cross.outputComparison.status !== 'mismatch',
      stateEquivalent: cross.stateComparison.status !== 'mismatch',
    };
  }
}

// ============================================================
// 証明書の表示フォーマッター
// ============================================================

export function formatCertificate(cert: ProofCertificate): string {
  const lines: string[] = [];

  lines.push('');
  lines.push('================================================================');
  lines.push('  PROOF CERTIFICATE - Modernization Correctness');
  lines.push('================================================================');
  lines.push('');
  lines.push(`  Certificate ID:   ${cert.certificateId}`);
  lines.push(`  Issued At:        ${cert.issuedAt}`);
  lines.push(`  Source Program:    ${cert.sourceProgramId}`);
  lines.push(`  Target Language:   ${cert.targetLanguage}`);
  lines.push(`  Status:            ${cert.status.toUpperCase()}`);
  lines.push('');

  // Property Preservation
  lines.push('--- Property Preservation ---');
  lines.push('');
  for (const entry of cert.propertyPreservation) {
    const icon = entry.preserved ? '[PASS]' : '[FAIL]';
    lines.push(`  ${icon} ${entry.propertyId}: ${entry.description}`);
    lines.push(`         Source: ${entry.sourceStatus}, Target: ${entry.targetStatus}`);
    lines.push(`         ${entry.message}`);
  }
  lines.push('');

  // Cross Verification
  lines.push('--- Cross Verification ---');
  lines.push('');
  lines.push(`  Output Comparison:  ${cert.crossVerification.outputComparison.status}`);
  if (cert.crossVerification.outputComparison.mismatches.length > 0) {
    for (const m of cert.crossVerification.outputComparison.mismatches) {
      lines.push(`    Line ${m.lineIndex}: ${m.detail}`);
      lines.push(`      Source: "${m.sourceLine}"`);
      lines.push(`      Target: "${m.targetLine}"`);
    }
  }
  lines.push(`  State Comparison:   ${cert.crossVerification.stateComparison.status}`);
  if (cert.crossVerification.stateComparison.comparisons.length > 0) {
    for (const c of cert.crossVerification.stateComparison.comparisons) {
      const icon = c.match ? '[=]' : '[!]';
      lines.push(`    ${icon} ${c.varName}: src=${c.sourceValue} tgt=${c.targetValue}`);
    }
  }
  lines.push('');

  // Summary
  lines.push('--- Summary ---');
  lines.push('');
  lines.push(`  Total Properties:     ${cert.summary.totalProperties}`);
  lines.push(`  Preserved:            ${cert.summary.preservedProperties}`);
  lines.push(`  Violated:             ${cert.summary.violatedProperties}`);
  lines.push(`  Skipped:              ${cert.summary.skippedProperties}`);
  lines.push(`  Preservation Rate:    ${(cert.summary.preservationRate * 100).toFixed(1)}%`);
  lines.push(`  Output Equivalent:    ${cert.summary.outputEquivalent}`);
  lines.push(`  State Equivalent:     ${cert.summary.stateEquivalent}`);
  lines.push('');
  lines.push('================================================================');

  return lines.join('\n');
}
