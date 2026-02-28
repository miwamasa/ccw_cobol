/-!
  # Foundation Types for COBOL Formal Verification

  COBOL type system (PIC clause) の Lean 4 形式化。
  固定小数点数型、境界付き文字列型、ループ補助関数を定義する。

  ## Types
  - `FixedDecimal` : COBOL PIC 9(n)V9(m) 固定小数点数
  - `BoundedString` : COBOL PIC X(n) 固定長文字列
  - `PicSpec` : PIC句の仕様 (桁数・符号)
-/

namespace CobolVerification

-- ============================================================
-- COBOL PIC Clause Specification
-- ============================================================

/-- PIC句の仕様: 整数桁数、小数桁数、符号有無 -/
structure PicSpec where
  integerDigits : Nat
  decimalDigits : Nat
  signed : Bool := false
  deriving Repr, BEq, DecidableEq

/-- PIC句から導出される値の上限 -/
def PicSpec.maxValue (p : PicSpec) : Int :=
  (10 ^ (p.integerDigits + p.decimalDigits)) - 1

/-- PIC句から導出される値の下限 -/
def PicSpec.minValue (p : PicSpec) : Int :=
  if p.signed then -(p.maxValue) else 0

/-- PIC句のスケール (10^decimalDigits) -/
def PicSpec.scale (p : PicSpec) : Nat :=
  10 ^ p.decimalDigits

-- ============================================================
-- Fixed-point Decimal (COBOL numeric)
-- ============================================================

/-- COBOL固定小数点数: 内部値はスケーリングされた整数
    例: PIC 9(7)V99, value 12345.67 → rawValue = 1234567, scale = 100 -/
structure FixedDecimal where
  rawValue : Int
  pic : PicSpec
  deriving Repr, BEq

namespace FixedDecimal

/-- 実際の値を有理数で取得 -/
def toRat (fd : FixedDecimal) : Rat :=
  ⟨fd.rawValue, fd.pic.scale⟩

/-- 整数値から FixedDecimal を生成 -/
def ofInt (n : Int) (p : PicSpec) : FixedDecimal :=
  { rawValue := n * p.scale, pic := p }

/-- ゼロ値 -/
def zero (p : PicSpec) : FixedDecimal :=
  { rawValue := 0, pic := p }

/-- 加算 (同一PIC) -/
def add (a b : FixedDecimal) : FixedDecimal :=
  { rawValue := a.rawValue + b.rawValue, pic := a.pic }

/-- 減算 (同一PIC) -/
def sub (a b : FixedDecimal) : FixedDecimal :=
  { rawValue := a.rawValue - b.rawValue, pic := a.pic }

/-- 比較: ≥ -/
def ge (a b : FixedDecimal) : Prop :=
  a.rawValue ≥ b.rawValue

/-- 比較: > -/
def gt (a b : FixedDecimal) : Prop :=
  a.rawValue > b.rawValue

/-- 比較: < -/
def lt (a b : FixedDecimal) : Prop :=
  a.rawValue < b.rawValue

/-- 比較: ≤ -/
def le (a b : FixedDecimal) : Prop :=
  a.rawValue ≤ b.rawValue

instance : Add FixedDecimal := ⟨FixedDecimal.add⟩
instance : Sub FixedDecimal := ⟨FixedDecimal.sub⟩
instance : LE FixedDecimal := ⟨FixedDecimal.le⟩
instance : LT FixedDecimal := ⟨FixedDecimal.lt⟩

/-- PIC句の範囲内であることの述語 -/
def inRange (fd : FixedDecimal) : Prop :=
  fd.pic.minValue ≤ fd.rawValue ∧ fd.rawValue ≤ fd.pic.maxValue

/-- 丸め: rawValueをPIC精度に丸める (半数切り上げ) -/
def round (fd : FixedDecimal) (targetPic : PicSpec) : FixedDecimal :=
  if targetPic.decimalDigits ≥ fd.pic.decimalDigits then
    -- 精度が同じか高い場合: スケーリングのみ
    let scaleDiff := targetPic.scale / fd.pic.scale
    { rawValue := fd.rawValue * scaleDiff, pic := targetPic }
  else
    -- 精度が低い場合: 丸めが必要
    let scaleDiff := fd.pic.scale / targetPic.scale
    let half := scaleDiff / 2
    { rawValue := (fd.rawValue + half) / scaleDiff, pic := targetPic }

/-- 丸め誤差の上限 -/
def maxRoundingError (p : PicSpec) : Rat :=
  ⟨1, 2 * p.scale⟩

end FixedDecimal

-- ============================================================
-- Bounded String (COBOL alphanumeric)
-- ============================================================

/-- COBOL PIC X(n) の固定長文字列 -/
structure BoundedString where
  value : String
  maxLen : Nat
  h_bound : value.length ≤ maxLen
  deriving Repr

namespace BoundedString

/-- 空文字列 -/
def empty (n : Nat) : BoundedString :=
  { value := "", maxLen := n, h_bound := by omega }

/-- 文字列の長さは常にmaxLen以下 -/
theorem length_le_max (bs : BoundedString) : bs.value.length ≤ bs.maxLen :=
  bs.h_bound

end BoundedString

-- ============================================================
-- Loop Helper (guarantees termination)
-- ============================================================

/-- fuel付きループ反復: 最大fuel回のステップで停止 -/
def loopIterate (init : α) (step : α → α) (done : α → Bool) (fuel : Nat) : α × Nat :=
  match fuel with
  | 0 => (init, 0)
  | n + 1 =>
    if done init then (init, 0)
    else
      let (result, iters) := loopIterate (step init) step done n
      (result, iters + 1)

/-- loopIterateは高々fuel回実行される -/
theorem loopIterate_bounded (init : α) (step : α → α) (done : α → Bool) (fuel : Nat) :
    (loopIterate init step done fuel).2 ≤ fuel := by
  induction fuel generalizing init with
  | zero => simp [loopIterate]
  | succ n ih =>
    simp only [loopIterate]
    split
    · omega
    · have := ih (step init)
      omega

end CobolVerification
