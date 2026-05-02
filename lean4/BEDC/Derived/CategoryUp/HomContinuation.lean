import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ContinuationMorphism_comp_tail_CategoryHomCarrier {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    UnaryHistory a -> UnaryHistory c -> UnaryHistory left.tail -> UnaryHistory right.tail ->
      CategoryHomCarrier a c (ContinuationMorphism_comp_closed left right).tail := by
  intro sourceCarrier targetCarrier leftTailCarrier rightTailCarrier
  exact And.intro sourceCarrier
    (And.intro targetCarrier
      (And.intro
        (unary_append_closed leftTailCarrier rightTailCarrier)
        (ContinuationMorphism_comp_closed left right).rel))

end BEDC.Derived.CategoryUp
