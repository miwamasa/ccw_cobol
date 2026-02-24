/**
 * Cross Verifier - 元COBOLと生成コードの同値性検証
 *
 * モダナイゼーションの核心: 元プログラムと変換後のプログラムが
 * 同じ入力に対して同じ振る舞いをするかどうかを検証する。
 *
 * 検証方法:
 * 1. 元COBOLプログラムをインタプリタで実行しトレースを収集
 * 2. 生成されたTypeScriptコードをシミュレーション実行
 * 3. 両方の結果に対してプロパティセットを検証
 * 4. Proof Certificate を生成
 *
 * この POC では、生成コードのシミュレーション実行として
 * 元のインタプリタの実行結果を「参照実装」とし、
 * 入力を変えた複数実行での振る舞い一致を検証する。
 */

import { CobolProgram } from './ast';
import { CobolInterpreter, ExecutionResult } from './interpreter';
import { ExecutionTracer } from './tracer';
import { PropertySet } from './properties';
import { PropertyVerifier, VerificationReport } from './verifier';
import {
  ProofCertificate, ProofCertificateBuilder, formatCertificate,
} from './proof-certificate';
import { formatCobolValue, CobolValue } from './types';

// ============================================================
// テスト入力: プログラムの入力データを変えて複数回実行
// ============================================================

export interface TestInput {
  /** テスト名 */
  readonly name: string;
  /** 変数の初期値を上書き（変数名 → 数値 or 文字列） */
  readonly overrides: ReadonlyMap<string, number | string>;
}

// ============================================================
// クロス検証の結果
// ============================================================

export interface CrossVerificationSuite {
  /** 元プログラムID */
  readonly programId: string;
  /** テスト入力ごとの結果 */
  readonly testResults: readonly TestCaseResult[];
  /** メインの Proof Certificate（デフォルト入力） */
  readonly mainCertificate: ProofCertificate;
  /** 全テストで証明書が valid か */
  readonly allValid: boolean;
}

export interface TestCaseResult {
  readonly testName: string;
  readonly sourceReport: VerificationReport;
  readonly certificate: ProofCertificate;
  readonly sourceOutput: string[];
  readonly sourceState: Map<string, string>;
}

// ============================================================
// クロス検証エンジン
// ============================================================

export class CrossVerifier {
  private program: CobolProgram;
  private propertySet: PropertySet;

  constructor(program: CobolProgram, propertySet: PropertySet) {
    this.program = program;
    this.propertySet = propertySet;
  }

  /**
   * デフォルト入力で検証を実行し Proof Certificate を生成
   */
  verifyDefault(): ProofCertificate {
    // 元プログラムを実行
    const { result, tracer } = this.executeProgram(this.program);

    // プロパティ検証
    const verifier = new PropertyVerifier(
      tracer.getEvents(),
      result.variables,
      result.displayOutput
    );
    const report = verifier.verify(this.propertySet);

    // 出力と状態を収集
    const stateMap = this.variablesToStringMap(result.variables);

    // Proof Certificate 生成
    const builder = new ProofCertificateBuilder(
      this.program.programId,
      'TypeScript',
      this.propertySet,
      report
    );

    return builder
      .withSourceOutput(result.displayOutput)
      .withSourceState(stateMap)
      .build();
  }

  /**
   * 複数テスト入力でクロス検証スイートを実行
   */
  verifyWithTestInputs(testInputs: readonly TestInput[]): CrossVerificationSuite {
    const testResults: TestCaseResult[] = [];

    // デフォルト入力での検証
    const mainCert = this.verifyDefault();

    // 追加テスト入力での検証
    for (const input of testInputs) {
      const modifiedProgram = this.applyOverrides(this.program, input.overrides);
      const { result, tracer } = this.executeProgram(modifiedProgram);

      const verifier = new PropertyVerifier(
        tracer.getEvents(),
        result.variables,
        result.displayOutput
      );
      const report = verifier.verify(this.propertySet);
      const stateMap = this.variablesToStringMap(result.variables);

      const cert = new ProofCertificateBuilder(
        this.program.programId,
        'TypeScript',
        this.propertySet,
        report
      )
        .withSourceOutput(result.displayOutput)
        .withSourceState(stateMap)
        .build();

      testResults.push({
        testName: input.name,
        sourceReport: report,
        certificate: cert,
        sourceOutput: result.displayOutput,
        sourceState: stateMap,
      });
    }

    const allValid = mainCert.status === 'valid' &&
      testResults.every(r => r.certificate.status === 'valid');

    return {
      programId: this.program.programId,
      testResults,
      mainCertificate: mainCert,
      allValid,
    };
  }

  // ============================================================
  // ヘルパーメソッド
  // ============================================================

  private executeProgram(program: CobolProgram): { result: ExecutionResult; tracer: ExecutionTracer } {
    const tracer = new ExecutionTracer();
    const interpreter = new CobolInterpreter(tracer);
    const result = interpreter.execute(program);
    return { result, tracer };
  }

  private variablesToStringMap(variables: Map<string, CobolValue>): Map<string, string> {
    const map = new Map<string, string>();
    for (const [name, value] of variables) {
      map.set(name, formatCobolValue(value));
    }
    return map;
  }

  /**
   * プログラムのデータ項目にオーバーライド値を適用した新しいプログラムを生成
   */
  private applyOverrides(
    program: CobolProgram,
    overrides: ReadonlyMap<string, number | string>
  ): CobolProgram {
    const newDataItems = program.dataItems.map(item => {
      const override = overrides.get(item.name);
      if (override !== undefined) {
        return { ...item, value: override };
      }
      return item;
    });

    return {
      ...program,
      dataItems: newDataItems,
    };
  }
}

// ============================================================
// クロス検証結果のフォーマッター
// ============================================================

export function formatCrossVerificationSuite(suite: CrossVerificationSuite): string {
  const lines: string[] = [];

  lines.push('');
  lines.push('================================================================');
  lines.push('  CROSS-VERIFICATION SUITE');
  lines.push('================================================================');
  lines.push('');
  lines.push(`  Program:    ${suite.programId}`);
  lines.push(`  Test Cases: ${suite.testResults.length + 1} (default + ${suite.testResults.length} additional)`);
  lines.push(`  All Valid:  ${suite.allValid}`);
  lines.push('');

  // デフォルト入力の結果
  lines.push('--- Default Input ---');
  lines.push(`  Status: ${suite.mainCertificate.status}`);
  lines.push(`  Properties: ${suite.mainCertificate.summary.preservedProperties}/${suite.mainCertificate.summary.totalProperties} preserved`);
  lines.push('');

  // 各テスト入力の結果
  for (const result of suite.testResults) {
    lines.push(`--- Test: ${result.testName} ---`);
    lines.push(`  Status: ${result.certificate.status}`);
    lines.push(`  Properties: ${result.certificate.summary.preservedProperties}/${result.certificate.summary.totalProperties} preserved`);

    const failedProps = result.sourceReport.results.filter(r => r.status === 'failed');
    if (failedProps.length > 0) {
      lines.push('  Failures:');
      for (const fp of failedProps) {
        lines.push(`    [FAIL] ${fp.propertyId}: ${fp.message}`);
      }
    }
    lines.push('');
  }

  lines.push('================================================================');

  return lines.join('\n');
}
