/-!
  # Formal Specification: LOAN-CALC

  Auto-generated Lean 4 formalization of the COBOL loan-calculation program.
  This module defines the denotational semantics of the program,
  enabling machine-checkable proofs of program properties.

  ## COBOL Source (modeled)
  ```
  PROGRAM-ID. LOAN-CALC.
  WORKING-STORAGE SECTION.
    01 WS-PRINCIPAL      PIC S9(7)V99  VALUE 100000.00.
    01 WS-ANNUAL-RATE    PIC 9(2)V9(4) VALUE 3.5000.
    01 WS-MONTHLY-RATE   PIC 9(2)V9(6) VALUE 0.
    01 WS-MONTHS         PIC 9(3)      VALUE 360.
    01 WS-PAYMENT        PIC 9(7)V99   VALUE 0.
    01 WS-TOTAL-INTEREST PIC 9(9)V99   VALUE 0.
    01 WS-BALANCE        PIC 9(9)V99   VALUE 0.
    01 WS-INTEREST-AMT   PIC 9(7)V99   VALUE 0.
    01 WS-PRINCIPAL-AMT  PIC 9(7)V99   VALUE 0.
    01 WS-MONTH-CTR      PIC 9(3)      VALUE 0.
    01 WS-STATUS         PIC X(10)     VALUE "ACTIVE".
    01 WS-TEMP           PIC 9(9)V9(4) VALUE 0.
  PROCEDURE DIVISION.
    PERFORM CALC-MONTHLY-RATE.
    PERFORM CALC-PAYMENT.
    MOVE WS-PRINCIPAL TO WS-BALANCE.
    PERFORM CALC-AMORTIZATION
      VARYING WS-MONTH-CTR FROM 1 BY 1
      UNTIL WS-MONTH-CTR > 12.
    ...
  ```

  ## Structure
  - `ProgramState` : Working-Storage Section の形式化
  - `initialState` : VALUE句による初期状態
  - `sem_*`        : 各パラグラフの表示的意味論
  - `execute`      : プログラム全体の意味論
-/

import CobolVerification.Foundation

namespace CobolVerification.LoanCalc

open CobolVerification

-- ============================================================
-- PIC Specifications
-- ============================================================

/-- WS-PRINCIPAL: PIC S9(7)V99 -/
def pic_principal : PicSpec := { integerDigits := 7, decimalDigits := 2, signed := true }

/-- WS-ANNUAL-RATE: PIC 9(2)V9(4) -/
def pic_annual_rate : PicSpec := { integerDigits := 2, decimalDigits := 4 }

/-- WS-MONTHLY-RATE: PIC 9(2)V9(6) -/
def pic_monthly_rate : PicSpec := { integerDigits := 2, decimalDigits := 6 }

/-- WS-MONTHS: PIC 9(3) -/
def pic_months : PicSpec := { integerDigits := 3, decimalDigits := 0 }

/-- WS-PAYMENT: PIC 9(7)V99 -/
def pic_payment : PicSpec := { integerDigits := 7, decimalDigits := 2 }

/-- WS-TOTAL-INTEREST: PIC 9(9)V99 -/
def pic_total_interest : PicSpec := { integerDigits := 9, decimalDigits := 2 }

/-- WS-BALANCE: PIC 9(9)V99 -/
def pic_balance : PicSpec := { integerDigits := 9, decimalDigits := 2 }

/-- WS-INTEREST-AMT: PIC 9(7)V99 -/
def pic_interest_amt : PicSpec := { integerDigits := 7, decimalDigits := 2 }

/-- WS-PRINCIPAL-AMT: PIC 9(7)V99 -/
def pic_principal_amt : PicSpec := { integerDigits := 7, decimalDigits := 2 }

/-- WS-MONTH-CTR: PIC 9(3) -/
def pic_month_ctr : PicSpec := { integerDigits := 3, decimalDigits := 0 }

/-- WS-TEMP: PIC 9(9)V9(4) -/
def pic_temp : PicSpec := { integerDigits := 9, decimalDigits := 4 }

-- ============================================================
-- Program State (DATA DIVISION formalization)
-- ============================================================

/-- Complete program state corresponding to WORKING-STORAGE SECTION -/
structure ProgramState where
  /-- WS-PRINCIPAL: 元金 (PIC S9(7)V99) -/
  ws_principal : FixedDecimal
  /-- WS-ANNUAL-RATE: 年利率 (PIC 9(2)V9(4)) -/
  ws_annual_rate : FixedDecimal
  /-- WS-MONTHLY-RATE: 月利率 (PIC 9(2)V9(6)) -/
  ws_monthly_rate : FixedDecimal
  /-- WS-MONTHS: 返済月数 (PIC 9(3)) -/
  ws_months : FixedDecimal
  /-- WS-PAYMENT: 月次返済額 (PIC 9(7)V99) -/
  ws_payment : FixedDecimal
  /-- WS-TOTAL-INTEREST: 累計利息 (PIC 9(9)V99) -/
  ws_total_interest : FixedDecimal
  /-- WS-BALANCE: 残高 (PIC 9(9)V99) -/
  ws_balance : FixedDecimal
  /-- WS-INTEREST-AMT: 月次利息額 (PIC 9(7)V99) -/
  ws_interest_amt : FixedDecimal
  /-- WS-PRINCIPAL-AMT: 月次元金充当額 (PIC 9(7)V99) -/
  ws_principal_amt : FixedDecimal
  /-- WS-MONTH-CTR: 月カウンタ (PIC 9(3)) -/
  ws_month_ctr : FixedDecimal
  /-- WS-STATUS: ステータス (PIC X(10)) -/
  ws_status : String
  /-- WS-TEMP: 一時変数 (PIC 9(9)V9(4)) -/
  ws_temp : FixedDecimal
  deriving Repr

-- ============================================================
-- Initial State (VALUE clauses)
-- ============================================================

/-- Initial state from COBOL VALUE clauses -/
def initialState : ProgramState := {
  ws_principal      := { rawValue := 10000000, pic := pic_principal }       -- 100000.00
  ws_annual_rate    := { rawValue := 35000,    pic := pic_annual_rate }     -- 3.5000
  ws_monthly_rate   := FixedDecimal.zero pic_monthly_rate                   -- 0.000000
  ws_months         := { rawValue := 360,      pic := pic_months }          -- 360
  ws_payment        := FixedDecimal.zero pic_payment                        -- 0.00
  ws_total_interest := FixedDecimal.zero pic_total_interest                 -- 0.00
  ws_balance        := FixedDecimal.zero pic_balance                        -- 0.00
  ws_interest_amt   := FixedDecimal.zero pic_interest_amt                   -- 0.00
  ws_principal_amt  := FixedDecimal.zero pic_principal_amt                  -- 0.00
  ws_month_ctr      := FixedDecimal.zero pic_month_ctr                     -- 0
  ws_status         := "ACTIVE"
  ws_temp           := FixedDecimal.zero pic_temp                           -- 0.0000
}

-- ============================================================
-- Type Constraints (PIC clause invariants)
-- ============================================================

/-- WS-PRINCIPAL: PIC S9(7)V99 → range [-999999999, 999999999]
    (rawValue is scaled by 100) -/
axiom type_constraint_principal :
  ∀ (s : ProgramState),
  s.ws_principal.rawValue ≥ pic_principal.minValue ∧
  s.ws_principal.rawValue ≤ pic_principal.maxValue

/-- WS-ANNUAL-RATE: PIC 9(2)V9(4) → unsigned, range [0, 999999] -/
axiom type_constraint_annual_rate :
  ∀ (s : ProgramState),
  s.ws_annual_rate.rawValue ≥ 0 ∧
  s.ws_annual_rate.rawValue ≤ pic_annual_rate.maxValue

/-- WS-MONTHLY-RATE: PIC 9(2)V9(6) → unsigned, range [0, 99999999] -/
axiom type_constraint_monthly_rate :
  ∀ (s : ProgramState),
  s.ws_monthly_rate.rawValue ≥ 0 ∧
  s.ws_monthly_rate.rawValue ≤ pic_monthly_rate.maxValue

/-- WS-TOTAL-INTEREST: PIC 9(9)V99 → unsigned, range [0, 99999999999] -/
axiom type_constraint_total_interest :
  ∀ (s : ProgramState),
  s.ws_total_interest.rawValue ≥ 0 ∧
  s.ws_total_interest.rawValue ≤ pic_total_interest.maxValue

/-- WS-BALANCE: PIC 9(9)V99 → unsigned, range [0, 99999999999] -/
axiom type_constraint_balance :
  ∀ (s : ProgramState),
  s.ws_balance.rawValue ≥ 0 ∧
  s.ws_balance.rawValue ≤ pic_balance.maxValue

/-- WS-PAYMENT: PIC 9(7)V99 → unsigned, range [0, 999999999] -/
axiom type_constraint_payment :
  ∀ (s : ProgramState),
  s.ws_payment.rawValue ≥ 0 ∧
  s.ws_payment.rawValue ≤ pic_payment.maxValue

/-- WS-MONTH-CTR: PIC 9(3) → unsigned, range [0, 999] -/
axiom type_constraint_month_ctr :
  ∀ (s : ProgramState),
  s.ws_month_ctr.rawValue ≥ 0 ∧
  s.ws_month_ctr.rawValue ≤ pic_month_ctr.maxValue

-- ============================================================
-- Semantic Functions (PROCEDURE DIVISION paragraphs)
-- ============================================================

/--
  Paragraph: CALC-MONTHLY-RATE
  COMPUTE WS-MONTHLY-RATE ROUNDED = WS-ANNUAL-RATE / 100 / 12

  月利 = 年利 / 100 / 12 = 年利 / 1200

  In fixed-point: the division is modeled as an operation on
  rawValues with appropriate scaling. Since this involves division
  (nonlinear), we model it abstractly:
    result_raw = (annual_rate_raw * monthly_rate_scale) / (1200 * annual_rate_scale)
-/
def sem_calc_monthly_rate (s : ProgramState) (result_raw : Int)
    (h_div : result_raw * 1200 * pic_annual_rate.scale =
             s.ws_annual_rate.rawValue * pic_monthly_rate.scale ∨
             -- Allow rounding error of ±1 in raw value
             (result_raw * 1200 * pic_annual_rate.scale -
              s.ws_annual_rate.rawValue * pic_monthly_rate.scale).natAbs ≤
             1200 * pic_annual_rate.scale) :
    ProgramState :=
  { s with ws_monthly_rate := { rawValue := result_raw, pic := pic_monthly_rate } }

/--
  Paragraph: CALC-PAYMENT (simplified model)
  COMPUTE WS-TEMP = WS-MONTHLY-RATE * WS-PRINCIPAL
  COMPUTE WS-PAYMENT ROUNDED = WS-TEMP
-/
def sem_calc_payment (s : ProgramState) (payment_raw : Int)
    (h_payment : payment_raw ≥ 0) :
    ProgramState :=
  { s with
    ws_payment := { rawValue := payment_raw, pic := pic_payment }
    ws_temp := { rawValue := payment_raw * pic_temp.scale / pic_payment.scale, pic := pic_temp } }

/--
  Paragraph: CALC-AMORTIZATION (one iteration)
  COMPUTE WS-INTEREST-AMT ROUNDED = WS-BALANCE * WS-MONTHLY-RATE
  COMPUTE WS-PRINCIPAL-AMT = WS-PAYMENT - WS-INTEREST-AMT
  SUBTRACT WS-PRINCIPAL-AMT FROM WS-BALANCE
  ADD WS-INTEREST-AMT TO WS-TOTAL-INTEREST
-/
def sem_calc_amortization_step (s : ProgramState) (interest_raw : Int)
    (h_interest : interest_raw ≥ 0) :
    ProgramState :=
  let principal_raw := s.ws_payment.rawValue - interest_raw
  { s with
    ws_interest_amt   := { rawValue := interest_raw, pic := pic_interest_amt }
    ws_principal_amt  := { rawValue := principal_raw, pic := pic_principal_amt }
    ws_balance        := { rawValue := s.ws_balance.rawValue - principal_raw, pic := pic_balance }
    ws_total_interest := { rawValue := s.ws_total_interest.rawValue + interest_raw,
                           pic := pic_total_interest }
    ws_month_ctr      := { rawValue := s.ws_month_ctr.rawValue + 1, pic := pic_month_ctr } }

-- ============================================================
-- Key Predicates for Properties
-- ============================================================

/-- 全フィールドがPIC範囲内であること -/
def allFieldsInRange (s : ProgramState) : Prop :=
  s.ws_total_interest.rawValue ≥ 0 ∧
  s.ws_balance.rawValue ≥ 0 ∧
  s.ws_payment.rawValue ≥ 0 ∧
  s.ws_monthly_rate.rawValue ≥ 0

/-- 月利が1未満 (rawValue < 1 * scale = 1000000) -/
def monthlyRateLessThanOne (s : ProgramState) : Prop :=
  s.ws_monthly_rate.rawValue < pic_monthly_rate.scale

/-- WS-PRINCIPAL-AMT + WS-INTEREST-AMT = WS-PAYMENT (raw value level) -/
def paymentDecomposition (s : ProgramState) : Prop :=
  s.ws_principal_amt.rawValue + s.ws_interest_amt.rawValue = s.ws_payment.rawValue

end CobolVerification.LoanCalc
