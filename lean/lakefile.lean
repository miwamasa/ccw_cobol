-- lakefile.lean
-- Lean 4 project configuration for COBOL formal verification
import Lake
open Lake DSL

package «cobol-verification» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «CobolVerification» where
  srcDir := "."
  roots := #[
    `CobolVerification.Foundation,
    `CobolVerification.LoanCalc,
    `CobolVerification.LoanCalcProofs,
    `CobolVerification.SmtBridge
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
