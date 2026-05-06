import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem GeomBound_cauchy_product_row_closed {a b : Nat -> BHist} {r K L : BHist} :
    GeomBound a r K -> GeomBound b r L ->
      GeomBound (fun n : Nat => append (a n) (b n)) r (append K L) := by
  intro leftBound rightBound
  exact And.intro leftBound.left
    (And.intro (unary_append_closed leftBound.right.left rightBound.right.left)
      (fun n : Nat =>
        ComplexHistoryCarrier_append_unary_closed (leftBound.right.right n)
          (ComplexHistoryCarrier_unary (rightBound.right.right n))))

end BEDC.Derived.ConvergenceRadiusUp
