import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ConvRadCheckedRowReduct_tail_shift_public_boundary
    {a : Nat -> BHist} {z0 R q : BHist} :
    ConvRadCheckedRowReduct a z0 R -> UnaryHistory q ->
      ConvRadCheckedRowReduct a z0 R ∧
        PowerSeriesCarrier (fun n : Nat => append (a n) q) (append z0 q) ∧
          ConvRad (fun n : Nat => append (a n) q) R ∧
            ConvRad (fun n : Nat => append q (a n)) R := by
  intro checked qUnary
  have sourceRows :
      PowerSeriesCarrier (fun n : Nat => append (a n) q) (append z0 q) ∧
        PowerSeriesCarrier (fun n : Nat => append q (a n)) (append q z0) :=
    ConvRadSourceSpec_powerSeries_append_prepend_closed checked.left qUnary
  have ledgerRows :
      ConvRadLedgerPolicy a z0 R ∧ ConvRad (fun n : Nat => append (a n) q) R ∧
        ConvRad (fun n : Nat => append q (a n)) R :=
    ConvRadCheckedRowReduct_append_prepend_ledger checked qUnary
  exact ⟨checked, sourceRows.left, ledgerRows.right.left, ledgerRows.right.right⟩

end BEDC.Derived.ConvergenceRadiusUp
