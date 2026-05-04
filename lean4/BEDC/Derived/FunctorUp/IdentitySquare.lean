import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_identity_square_public_readback {p a id left right displayed : BHist} :
    UnaryHistory p -> UnaryHistory a -> Cont BHist.Empty BHist.Empty id ->
      Cont id BHist.Empty left -> Cont BHist.Empty id right ->
        CategoryHomCarrier (append p a) (append p a) displayed ->
          hsame left displayed ∧ hsame right displayed := by
  intro prefixCarrier sourceCarrier idRel leftRel rightRel displayedCarrier
  have idCarrier : CategoryHomCarrier (append p a) (append p a) id :=
    FunctorPrefixHomCarrier_identity_closed prefixCarrier sourceCarrier idRel
  have leftSame : hsame left id := cont_deterministic leftRel (cont_right_unit id)
  have rightSame : hsame right id := cont_left_unit_result rightRel
  have leftCarrier : CategoryHomCarrier (append p a) (append p a) left := by
    cases leftSame
    exact idCarrier
  have rightCarrier : CategoryHomCarrier (append p a) (append p a) right := by
    cases rightSame
    exact idCarrier
  exact
    And.intro
      (CategoryHomCarrier_morphism_deterministic leftCarrier displayedCarrier)
      (CategoryHomCarrier_morphism_deterministic rightCarrier displayedCarrier)

end BEDC.Derived.FunctorUp
