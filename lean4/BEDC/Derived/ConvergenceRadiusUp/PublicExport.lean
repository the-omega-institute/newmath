import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ConvRadCheckedRowReduct_public_export {a : Nat -> BHist} {z0 R q : BHist} :
    ConvRadCheckedRowReduct a z0 R -> UnaryHistory q ->
      ConvRadLedgerPolicy a z0 R ∧
        PowerSeriesCarrier (fun n : Nat => append (a n) q) (append z0 q) ∧
          ConvRad (fun n : Nat => append (a n) q) R ∧
            ConvRad (fun n : Nat => append q (a n)) R := by
  intro checked qUnary
  have sourceCarrier : PowerSeriesCarrier a z0 := checked.left.left
  have exported := ConvRadCheckedRowReduct_append_prepend_ledger checked qUnary
  exact
    ⟨exported.left, PowerSeriesCarrier_append_unary_closed sourceCarrier qUnary,
      exported.right.left, exported.right.right⟩

end BEDC.Derived.ConvergenceRadiusUp
