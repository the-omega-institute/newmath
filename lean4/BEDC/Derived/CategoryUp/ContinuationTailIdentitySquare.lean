import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_tail_identity_square_closed {a b left right : BHist}
    (m : ContinuationMorphism a b) :
    Cont BHist.Empty m.tail left -> Cont m.tail BHist.Empty right ->
      hsame left right /\ Cont a left b /\ Cont a right b := by
  intro leftRel rightRel
  have leftSame : hsame left m.tail := cont_left_unit_result leftRel
  have rightSame : hsame right m.tail := cont_deterministic rightRel (cont_right_unit m.tail)
  have leftCont : Cont a left b := by
    cases leftSame
    exact m.rel
  have rightCont : Cont a right b := by
    cases rightSame
    exact m.rel
  exact And.intro (leftSame.trans rightSame.symm) (And.intro leftCont rightCont)

end BEDC.Derived.CategoryUp
