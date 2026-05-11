import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ConvRad_tail_shift_public_boundary {a : Nat -> BHist} {z0 R q : BHist} :
    ConvRadSourceSpec a z0 R -> UnaryHistory q ->
      SemanticNameCert (ConvRad (fun n : Nat => a (Nat.succ n)))
          (ConvRad (fun n : Nat => a (Nat.succ n)))
          (ConvRad (fun n : Nat => a (Nat.succ n))) hsame ∧
        ConvRad (fun n : Nat => a (Nat.succ n)) R ∧
          ConvRadCheckedRowReduct a z0 R ∧ ConvRadLedgerPolicy a z0 R ∧
            ConvRad (fun n : Nat => append (a (Nat.succ n)) q) R := by
  intro source qUnary
  have tailRadius : ConvRad (fun n : Nat => a (Nat.succ n)) R :=
    ConvRad_successor_coefficients_closed source.right
  have checked : ConvRadCheckedRowReduct a z0 R :=
    ConvRadSourceSpec_checkedRowReduct_readback source
  have ledger :=
    ConvRadCheckedRowReduct_append_prepend_ledger checked qUnary
  exact And.intro
    (ConvRad_semanticNameCert tailRadius)
    (And.intro tailRadius
      (And.intro checked
        (And.intro ledger.left
          (ConvRad_append_unary_coeff_closed tailRadius qUnary))))

end BEDC.Derived.ConvergenceRadiusUp
