# Lean 4 Formal Verification Guide for COBOL Programs

## Overview

This document describes how to set up and run the Lean 4 formal verification
of COBOL program properties. The Lean proofs complement the cvc5 SMT solver
verification by providing machine-checked proofs within a full dependent type
theory.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                  Verification Stack                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐  │
│  │ COBOL Source  │───→│  TypeScript  │───→│ SMT Verifier │  │
│  │  (AST)        │    │ Interpreter  │    │   (cvc5)     │  │
│  └──────────────┘    └──────┬───────┘    └──────┬───────┘  │
│         │                   │                    │          │
│         │            Trace Events          SMT Results      │
│         │                   │              (UNSAT/SAT)      │
│         ▼                   ▼                    │          │
│  ┌──────────────┐    ┌──────────────┐            │          │
│  │  Lean IR     │───→│ Lean 4 Files │◄───────────┘          │
│  │  Generator   │    │ (.lean)      │   SmtBridge.lean      │
│  └──────────────┘    └──────┬───────┘                       │
│                             │                               │
│                             ▼                               │
│                      ┌──────────────┐                       │
│                      │  Lean 4      │                       │
│                      │  Type Check  │                       │
│                      │  (lake build)│                       │
│                      └──────────────┘                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## Prerequisites

### 1. Install Lean 4

```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Verify installation
lean --version
# Expected: leanprover/lean4:v4.14.0 or later
```

### 2. Install Lake (Lean's build tool)

Lake is included with Lean 4 via elan. Verify:

```bash
lake --version
```

## Project Structure

```
lean/
├── lakefile.lean                       # Build configuration
├── lean-toolchain                      # Lean version pinning
└── CobolVerification/
    ├── Foundation.lean                 # Base types (FixedDecimal, BoundedString)
    ├── LoanCalc.lean                   # Program state & semantic functions
    ├── LoanCalcProofs.lean             # Property theorems & proofs
    └── SmtBridge.lean                  # cvc5 results as axioms
```

## Building and Checking Proofs

### Quick Start

```bash
cd lean/

# Download dependencies (mathlib) - first time only
lake update

# Build and type-check all proofs
lake build
```

If `lake build` succeeds with no errors, all proofs are machine-checked.

### Checking Individual Files

```bash
# Check only the foundation types
lake build CobolVerification.Foundation

# Check the program specification
lake build CobolVerification.LoanCalc

# Check the proofs
lake build CobolVerification.LoanCalcProofs

# Check the SMT bridge
lake build CobolVerification.SmtBridge
```

### Without Mathlib (Faster)

If you want to skip the mathlib dependency for faster builds,
edit `lakefile.lean` to remove the `require mathlib` line.
The core proofs in `Foundation.lean`, `LoanCalc.lean`, and
`LoanCalcProofs.lean` use only `omega` and `simp`, which are
built into Lean 4.

## File Descriptions

### Foundation.lean — Base Types

Defines the COBOL type system in Lean 4:

| Type | COBOL | Description |
|------|-------|-------------|
| `PicSpec` | PIC clause | Integer/decimal digits, signed flag |
| `FixedDecimal` | PIC 9(n)V9(m) | Fixed-point number with scaled integer |
| `BoundedString` | PIC X(n) | Fixed-length string |
| `loopIterate` | PERFORM UNTIL | Fuel-bounded loop with termination proof |

Key theorem:
```lean
theorem loopIterate_bounded :
  (loopIterate init step done fuel).2 ≤ fuel
```
This guarantees any COBOL loop terminates within the fuel bound.

### LoanCalc.lean — Program Specification

Formalizes the loan-calculation COBOL program:

**PIC Specifications:**
| Variable | PIC | Scale | Max Value |
|----------|-----|-------|-----------|
| WS-PRINCIPAL | S9(7)V99 | 100 | 999,999,999 |
| WS-ANNUAL-RATE | 9(2)V9(4) | 10,000 | 999,999 |
| WS-MONTHLY-RATE | 9(2)V9(6) | 1,000,000 | 99,999,999 |
| WS-BALANCE | 9(9)V99 | 100 | 99,999,999,999 |
| WS-PAYMENT | 9(7)V99 | 100 | 999,999,999 |
| WS-TOTAL-INTEREST | 9(9)V99 | 100 | 99,999,999,999 |

**Semantic Functions:**
- `sem_calc_monthly_rate` — COMPUTE WS-MONTHLY-RATE = ANNUAL-RATE / 1200
- `sem_calc_payment` — COMPUTE WS-PAYMENT = MONTHLY-RATE * PRINCIPAL
- `sem_calc_amortization_step` — One iteration of the amortization loop

**Type Constraint Axioms:**
- `type_constraint_annual_rate` — unsigned, ≤ 999,999
- `type_constraint_monthly_rate` — unsigned, ≤ 99,999,999
- `type_constraint_total_interest` — unsigned, ≤ 99,999,999,999
- `type_constraint_balance` — unsigned, ≤ 99,999,999,999
- etc.

### LoanCalcProofs.lean — Property Theorems

Machine-checkable proofs for all 13 properties:

| Property | Theorem | Strategy | Status |
|----------|---------|----------|--------|
| INV-01 base | `inv01_base` | `simp` | ✅ proven |
| INV-01 step | `inv01_step` | `omega` | ✅ proven |
| INV-02 base | `inv02_base` | `simp` | ✅ proven |
| INV-02 step | `inv02_step` | `omega` | ✅ proven |
| INV-03 | `inv03_monthly_rate_lt_one` | `omega` | ✅ proven |
| PRE-01 | `pre01_annual_rate_positive` | `simp` | ✅ proven |
| PRE-02 | `pre02_monthly_rate_positive` | `exact` | ✅ proven |
| POST-01 | `post01_monthly_rate_positive` | `exact` | ✅ proven |
| POST-02 | `post02_payment_positive` | `exact` | ✅ proven |
| REL-01 | `rel01_payment_decomposition` | `omega` | ✅ proven |
| PREC-01 | `prec01_monthly_rate_precision` | `exact` | ✅ proven |
| PREC-02 | `prec02_interest_precision` | `exact` | ✅ proven |
| LOOP-01 | `loop01_amortization_bounded` | structural | ✅ proven |

Additional structural lemmas:
- `amortization_total_interest_monotone` — total interest is non-decreasing
- `amortization_balance_decrease` — balance decreases by principal amount
- `amortization_ctr_increment` — counter increments by 1

### SmtBridge.lean — cvc5 Integration

Bridges cvc5 SMT solver results into the Lean proof system:

- SMT results are declared as `axiom`s, making the trust assumption explicit
- Each axiom documents the corresponding SMT-LIB 2 query
- `SmtEvidence` records track property ID, theory, strategy, and result
- `all_proven` theorem verifies all 15 evidence records are UNSAT

#### Trust Model

```
                   Trust Boundary
                        │
  ┌─────────────────────┼────────────────────────┐
  │ Lean Type Checker    │  cvc5 SMT Solver       │
  │ (fully trusted)      │  (trusted as oracle)   │
  │                      │                        │
  │ Structural proofs    │  UNSAT verdicts         │
  │ (LoanCalcProofs)     │  → axioms in SmtBridge │
  │                      │                        │
  │ omega, simp, exact   │  QF_LRA, QF_NRA,      │
  │ (no sorry)           │  QF_LIA                │
  └─────────────────────┼────────────────────────┘
                        │
```

- **LoanCalcProofs.lean** contains fully constructive proofs — no `sorry`, no `axiom`
  except the PIC type constraints (which are definitional)
- **SmtBridge.lean** encodes cvc5 results as axioms — these are trusted
- To remove SMT trust: replace each axiom in SmtBridge with a constructive Lean proof

## Proof Techniques

### 1. omega (Linear Integer Arithmetic)

Used for range bounds, monotonicity, and counter proofs:

```lean
theorem inv01_step (s : ProgramState) (interest_raw : Int)
    (ih : s.ws_total_interest.rawValue ≥ 0)
    (h_interest : interest_raw ≥ 0) :
    (sem_calc_amortization_step s interest_raw h_interest)
      .ws_total_interest.rawValue ≥ 0 := by
  simp [sem_calc_amortization_step]
  omega
```

The `omega` tactic decides Presburger arithmetic (linear integer arithmetic
with addition, subtraction, and constants).

### 2. simp (Simplification)

Used to unfold definitions and evaluate concrete values:

```lean
theorem inv01_base : initialState.ws_total_interest.rawValue ≥ 0 := by
  simp [initialState, FixedDecimal.zero]
```

### 3. Structural Recursion (Loop Bounds)

Loop bounds use the `loopIterate_bounded` theorem:

```lean
theorem loop01_amortization_bounded : ... := by
  exact loopIterate_bounded _ _ _ 12
```

### 4. Inductive Proofs

Data invariants use base case + inductive step pattern:

```
Base:  initialState satisfies P         (simp)
Step:  P(s) ∧ operation(s, s') → P(s')  (omega)
```

## Extending with New Properties

### Adding a New Data Invariant

1. Define the invariant in `LoanCalc.lean`:
```lean
def myInvariant (s : ProgramState) : Prop :=
  s.ws_my_var.rawValue ≥ 0
```

2. Prove base case in `LoanCalcProofs.lean`:
```lean
theorem my_inv_base : myInvariant initialState := by
  simp [myInvariant, initialState, FixedDecimal.zero]
```

3. Prove inductive step:
```lean
theorem my_inv_step (s : ProgramState)
    (ih : myInvariant s)
    (h_op : ...) :
    myInvariant (operation s ...) := by
  simp [myInvariant, operation]
  omega
```

### Adding a New COBOL Program

1. Define PIC specs in a new file (e.g., `MyProgram.lean`)
2. Define `ProgramState` structure with all working-storage variables
3. Define `initialState` from VALUE clauses
4. Define semantic functions for each paragraph
5. Create a proof file (`MyProgramProofs.lean`) with theorems

## Relationship to SMT Verification

| Aspect | Lean 4 | cvc5 SMT |
|--------|--------|----------|
| Trust base | Lean kernel (small, verified) | cvc5 solver (large, tested) |
| Proof format | Constructive terms | UNSAT certificate |
| Decidability | General (can express undecidable) | Decidable theories only |
| Automation | Tactics (omega, simp) | Fully automatic |
| Expressivity | Full dependent types | First-order + theories |
| Verification time | Seconds (type-checking) | Milliseconds (solving) |
| Human effort | Write proof scripts | Define property encodings |

**Recommended workflow:**
1. Use cvc5 for rapid property screening (milliseconds)
2. Use Lean for high-assurance proofs of critical properties
3. Use `SmtBridge.lean` to integrate both approaches

## Troubleshooting

### `lake build` fails with "unknown identifier"

Ensure imports are correct:
```lean
import CobolVerification.Foundation
import CobolVerification.LoanCalc
```

### `omega` fails

The property may involve nonlinear arithmetic. Options:
- Reformulate as linear (e.g., encode division as multiplication)
- Use `norm_num` for concrete numeric goals
- Use `nlinarith` (requires mathlib)
- Fall back to SMT bridge axiom

### Slow builds

- First build downloads mathlib (can take 10-30 minutes)
- Subsequent builds use cached oleans
- For faster iteration, remove the mathlib dependency if not needed

### `sorry` in proofs

`sorry` is a proof placeholder that always type-checks but makes
the proof incomplete. Search for `sorry` to find unfinished proofs:
```bash
grep -r "sorry" lean/CobolVerification/
```
The current codebase has **zero** `sorry` in `LoanCalcProofs.lean`.

## References

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Lean 4 Theorem Proving](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)
- [Tactics Reference](https://lean-lang.org/lean4/doc/tactics.html)
- [cvc5 SMT Solver](https://cvc5.github.io/)
