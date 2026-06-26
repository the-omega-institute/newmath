import Lake
open Lake DSL

package "bedc_quality_lab_formal" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`maxHeartbeats, 400000⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib Classifier where

@[default_target]
lean_lib MarginStability where

@[default_target]
lean_lib Ledger where

@[default_target]
lean_lib FiniteLedgerCoverage where
