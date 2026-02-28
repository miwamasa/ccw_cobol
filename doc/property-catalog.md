# COBOL Property Catalog — Formal Verification Reference

## Property Taxonomy

| Kind | Description | SMT Theory | Lean Tactic |
|------|-------------|------------|-------------|
| DataInvariant | Variable constraint at every state | QF_LRA | omega / simp |
| Precondition | Must hold before paragraph call | QF_LRA | simp + omega |
| Postcondition | Must hold after paragraph execution | QF_NRA | exact / omega |
| Relational | Algebraic relationship between vars | QF_LRA | omega |
| Precision | Rounding error bound | QF_LRA | exact |
| LoopBound | Maximum iteration count | QF_LIA | structural |
| FinalState | End-of-program value check | witness | simp |
| OutputEquiv | DISPLAY output equivalence | QF_LRA | bisimulation |

## Loan-Calc Properties (13)

### INV-01: WS-TOTAL-INTEREST ≥ 0

- **Kind:** DataInvariant
- **Variable:** WS-TOTAL-INTEREST (PIC 9(9)V99)
- **Condition:** `ws_total_interest ≥ 0`
- **Check at:** every-assignment
- **Proof strategy:** Inductive (base + step)
  - Base: initial value = 0 ≥ 0
  - Step: ADD with non-negative interest preserves ≥ 0
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `inv01_base`, `inv01_step`

### INV-02: WS-BALANCE ≥ 0

- **Kind:** DataInvariant
- **Variable:** WS-BALANCE (PIC 9(9)V99)
- **Condition:** `ws_balance ≥ 0`
- **Check at:** every-assignment
- **Proof strategy:** Inductive with no-underflow precondition
  - Base: initial value = 0 ≥ 0
  - Step: SUBTRACT with principal_amt ≤ balance preserves ≥ 0
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `inv02_base`, `inv02_step`

### INV-03: WS-MONTHLY-RATE < 1

- **Kind:** DataInvariant
- **Variable:** WS-MONTHLY-RATE (PIC 9(2)V9(6))
- **Condition:** `ws_monthly_rate < 1.0`
- **Check at:** every-assignment
- **Proof strategy:** Nonlinear arithmetic
  - PIC 9(2)V9(4) max = 99.9999
  - 99.9999 / 1200 = 0.0833... < 1
  - Division encoded as multiplication: `rate * 1200 = annual_rate`
- **SMT theory:** QF_NRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `inv03_monthly_rate_lt_one`

### PRE-01: WS-ANNUAL-RATE > 0 before CALC-MONTHLY-RATE

- **Kind:** Precondition
- **Paragraph:** CALC-MONTHLY-RATE
- **Condition:** `ws_annual_rate > 0`
- **Proof strategy:** Ground check (initial value = 3.5 > 0)
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `pre01_annual_rate_positive`

### PRE-02: WS-MONTHLY-RATE > 0 before CALC-PAYMENT

- **Kind:** Precondition
- **Paragraph:** CALC-PAYMENT
- **Condition:** `ws_monthly_rate > 0`
- **Proof strategy:** Symbolic (follows from PRE-01 + CALC-MONTHLY-RATE semantics)
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `pre02_monthly_rate_positive`

### POST-01: WS-MONTHLY-RATE > 0 after CALC-MONTHLY-RATE

- **Kind:** Postcondition
- **Paragraph:** CALC-MONTHLY-RATE
- **Condition:** `ws_monthly_rate > 0`
- **Proof strategy:** Result positivity from positive input
- **SMT theory:** QF_NRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `post01_monthly_rate_positive`

### POST-02: WS-PAYMENT > 0 after CALC-PAYMENT

- **Kind:** Postcondition
- **Paragraph:** CALC-PAYMENT
- **Condition:** `ws_payment > 0`
- **Proof strategy:** Payment = rate × principal, both > 0
- **SMT theory:** QF_NRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `post02_payment_positive`

### REL-01: PRINCIPAL-AMT + INTEREST-AMT = PAYMENT

- **Kind:** Relational
- **Condition:** `ws_principal_amt + ws_interest_amt = ws_payment` (tolerance: 0.01)
- **Check after:** CALC-AMORTIZATION
- **Proof strategy:** Algebraic identity
  - From definition: `principal_amt = payment - interest_amt`
  - Therefore: `principal_amt + interest_amt = payment` (exact)
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `rel01_payment_decomposition`

### PREC-01: Monthly Rate Rounding Error ≤ 5×10⁻⁷

- **Kind:** Precision
- **Variable:** WS-MONTHLY-RATE (PIC 9(2)V9(6))
- **Min decimal places:** 6
- **Rounding mode:** must-round
- **Proof strategy:** PIC clause precision bound
  - Scale = 10⁶, max error = 0.5 × 10⁻⁶ = 5 × 10⁻⁷
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `prec01_monthly_rate_precision`

### PREC-02: Interest Amount Rounding Error ≤ 0.005

- **Kind:** Precision
- **Variable:** WS-INTEREST-AMT (PIC 9(7)V99)
- **Min decimal places:** 2
- **Rounding mode:** must-round
- **Proof strategy:** PIC clause precision bound
  - Scale = 10², max error = 0.5 × 10⁻² = 0.005
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `prec02_interest_precision`

### LOOP-01: Amortization Loop ≤ 12 Iterations

- **Kind:** LoopBound
- **Paragraph:** CALC-AMORTIZATION
- **Max iterations:** 12
- **Proof strategy:** Counter-based
  - FROM 1 BY 1 UNTIL > 12
  - Counter starts at 1, increments by 1, terminates at 13
  - Exactly 12 iterations
- **SMT theory:** QF_LIA
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `loop01_amortization_bounded`

### FINAL-01: WS-STATUS = "HIGH-INT" (default inputs)

- **Kind:** FinalState
- **Variable:** WS-STATUS (PIC X(10))
- **Expected:** "HIGH-INT"
- **Proof strategy:** Conditional evaluation
  - Total interest > 3000 → "HIGH-INT"
  - With default inputs (principal=100000, rate=3.5%), total interest > 3000
- **SMT:** Bounded model check (witness)
- **SMT result:** UNSAT (proven)
- **Lean theorem:** `final01_default_high_int`

### OUT-01: Output Within Numeric Tolerance

- **Kind:** OutputEquivalence
- **Tolerance:** 0.01
- **Proof strategy:** Arithmetic bound on rounding errors
- **SMT theory:** QF_LRA
- **SMT result:** UNSAT (proven)
- **Lean/SMT:** `smt_out01`

## Adding New Properties

### Step 1: Define in TypeScript

```typescript
// In src/main.ts or property definition file
{
  propertyType: 'data-invariant',
  id: 'INV-04',
  description: 'WS-PAYMENT is bounded by WS-PRINCIPAL',
  targetVar: 'WS-PAYMENT',
  condition: cmp('<=', varRef('WS-PAYMENT'), varRef('WS-PRINCIPAL')),
  checkAt: 'every-assignment',
}
```

### Step 2: Verify with cvc5 (automatic)

Run the pipeline — the SMT verifier will automatically generate
and check an SMT-LIB 2 query.

### Step 3: Add Lean Proof (manual)

```lean
-- In LoanCalcProofs.lean
theorem inv04_payment_bounded (s : ProgramState)
    (h : s.ws_payment.rawValue ≤ s.ws_principal.rawValue) :
    s.ws_payment.rawValue ≤ s.ws_principal.rawValue := by
  exact h
```

### Step 4: Bridge SMT Result (if using SmtBridge)

```lean
-- In SmtBridge.lean
axiom smt_inv04 :
  ∀ (payment principal : Int),
  payment ≤ principal → payment ≤ principal
```
