/**
 * COBOL Type System - Type-Safe Representation
 * 
 * COBOLの暗黙的な型情報を、TypeScriptのDiscriminated Unionで明示的に表現する。
 * これがこのアプローチの核心：COBOLの曖昧さが型として捕捉される。
 */

// ============================================================
// PIC句の解析結果を表す型
// ============================================================

/** PIC句のカテゴリ（COBOLの暗黙的カテゴリを明示化） */
export type PicCategory = 
  | 'numeric'          // PIC 9(n)V9(m) - 数値
  | 'alphanumeric'     // PIC X(n) - 英数字
  | 'alphabetic'       // PIC A(n) - 英字のみ
  | 'numeric-edited'   // PIC Z(n)9.99 - 編集数値
  | 'alphanumeric-edited'; // PIC X(n)B - 編集英数字

/** 解析済みPIC句 */
export interface PicClause {
  readonly raw: string;              // 元のPIC文字列 e.g. "S9(5)V99"
  readonly category: PicCategory;
  readonly totalDigits: number;      // 整数部桁数
  readonly decimalDigits: number;    // 小数部桁数 (V以降)
  readonly isSigned: boolean;        // S付きか
  readonly size: number;             // バイト数
}

// ============================================================
// COBOL値の型安全な表現 (Discriminated Union)
// ============================================================

/** 固定小数点数値 - COBOLの核心的データ型 */
export interface FixedDecimalValue {
  readonly kind: 'fixed-decimal';
  /** 内部表現: 実際の値 × 10^scale で整数化した値 */
  readonly rawValue: bigint;
  /** 小数点以下桁数 */
  readonly scale: number;
  /** 整数部の最大桁数 */
  readonly integerDigits: number;
  /** 符号付きか */
  readonly signed: boolean;
}

/** 英数字文字列 - 固定長 */
export interface AlphanumericValue {
  readonly kind: 'alphanumeric';
  /** 内部バイト列（固定長、右側スペースパディング） */
  readonly bytes: string;
  /** 定義された長さ */
  readonly length: number;
}

/** グループ項目 - 構造体相当 */
export interface GroupValue {
  readonly kind: 'group';
  /** 子要素の順序付きマップ */
  readonly members: ReadonlyMap<string, CobolValue>;
  /** グループ全体のバイト長 */
  readonly length: number;
}

/** COBOL値のUnion型 */
export type CobolValue = FixedDecimalValue | AlphanumericValue | GroupValue;

// ============================================================
// 値の生成ヘルパー
// ============================================================

/** 固定小数点数値を生成 */
export function makeFixedDecimal(
  value: number,
  pic: PicClause
): FixedDecimalValue {
  const scale = pic.decimalDigits;
  const factor = 10 ** scale;
  // COBOLのTRUNCATIONルール: 桁数を超える部分は切り捨て
  const rawValue = BigInt(Math.trunc(value * factor));
  // maxIntVal is the max raw value: total capacity = integer digits + decimal digits
  const totalCapacity = pic.totalDigits + pic.decimalDigits;
  const maxIntVal = BigInt(10 ** totalCapacity) - 1n;
  const clampedRaw = rawValue > maxIntVal ? maxIntVal : 
                     (pic.isSigned && rawValue < -maxIntVal) ? -maxIntVal : rawValue;
  
  return {
    kind: 'fixed-decimal',
    rawValue: clampedRaw,
    scale,
    integerDigits: pic.totalDigits,
    signed: pic.isSigned,
  };
}

/** 英数字値を生成 */
export function makeAlphanumeric(
  value: string,
  length: number
): AlphanumericValue {
  // COBOLルール: 左詰め、右側スペースパディング、超過分は切り捨て
  const padded = value.padEnd(length, ' ').substring(0, length);
  return {
    kind: 'alphanumeric',
    bytes: padded,
    length,
  };
}

/** 固定小数点の実数値を取得 */
export function decimalToNumber(val: FixedDecimalValue): number {
  return Number(val.rawValue) / (10 ** val.scale);
}

/** COBOL値を表示用文字列に変換 */
export function formatCobolValue(val: CobolValue): string {
  switch (val.kind) {
    case 'fixed-decimal':
      return decimalToNumber(val).toFixed(val.scale);
    case 'alphanumeric':
      return val.bytes;
    case 'group':
      return `[GROUP: ${[...val.members.keys()].join(', ')}]`;
  }
}

// ============================================================
// PIC句パーサー
// ============================================================

export function parsePic(raw: string): PicClause {
  const upper = raw.toUpperCase().replace(/\s/g, '');
  let isSigned = false;
  let totalDigits = 0;
  let decimalDigits = 0;
  let inDecimal = false;
  let category: PicCategory = 'alphanumeric';
  let size = 0;
  let hasDigit = false;
  let hasAlpha = false;

  let i = 0;
  while (i < upper.length) {
    const ch = upper[i];
    if (ch === 'S') {
      isSigned = true;
      i++;
    } else if (ch === '9') {
      hasDigit = true;
      const count = parseRepeat(upper, i);
      if (inDecimal) decimalDigits += count.value;
      else totalDigits += count.value;
      size += count.value;
      i = count.nextIndex;
    } else if (ch === 'X') {
      hasAlpha = true;
      const count = parseRepeat(upper, i);
      size += count.value;
      i = count.nextIndex;
    } else if (ch === 'A') {
      hasAlpha = true;
      const count = parseRepeat(upper, i);
      size += count.value;
      i = count.nextIndex;
    } else if (ch === 'V') {
      inDecimal = true;
      i++;
    } else if (ch === 'Z' || ch === '.' || ch === ',' || ch === '-' || ch === '+' || ch === 'B') {
      // 編集文字: 簡略化のためスキップ
      const count = parseRepeat(upper, i);
      size += count.value;
      i = count.nextIndex;
    } else {
      i++;
    }
  }

  if (hasDigit && !hasAlpha) category = 'numeric';
  else if (!hasDigit && hasAlpha) category = 'alphanumeric'; // X and A are both alphanumeric category
  else if (hasDigit && hasAlpha) category = 'alphanumeric';
  else category = 'alphanumeric';

  return { raw, category, totalDigits, decimalDigits, isSigned, size };
}

function parseRepeat(s: string, pos: number): { value: number; nextIndex: number } {
  if (pos + 1 < s.length && s[pos + 1] === '(') {
    const closeIdx = s.indexOf(')', pos + 2);
    if (closeIdx !== -1) {
      const num = parseInt(s.substring(pos + 2, closeIdx), 10);
      return { value: isNaN(num) ? 1 : num, nextIndex: closeIdx + 1 };
    }
  }
  return { value: 1, nextIndex: pos + 1 };
}
