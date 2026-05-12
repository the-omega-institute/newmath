import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ConvRadCheckedRowReduct_prefix_window_stability {a : Nat -> BHist} {z0 R q : BHist} :
    ConvRadCheckedRowReduct a z0 R -> UnaryHistory q ->
      ConvRadCheckedRowReduct (fun n : Nat => append (a n) q) (append z0 q) R ∧
        ConvRad (fun n : Nat => append (a n) q) R := by
  intro checked qUnary
  have appendCarrier :
      PowerSeriesCarrier (fun n : Nat => append (a n) q) (append z0 q) :=
    PowerSeriesCarrier_append_unary_closed checked.left.left qUnary
  have appendRadius : ConvRad (fun n : Nat => append (a n) q) R :=
    ConvRad_append_unary_coeff_closed checked.left.right qUnary
  have appendSource :
      ConvRadSourceSpec (fun n : Nat => append (a n) q) (append z0 q) R :=
    And.intro appendCarrier appendRadius
  exact And.intro
    (ConvRadSourceSpec_checkedRowReduct_readback appendSource)
    appendRadius

end BEDC.Derived.ConvergenceRadiusUp
