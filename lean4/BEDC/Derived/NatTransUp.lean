import BEDC.Derived.FunctorUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp

theorem NatTransPrefixIdentity_naturality_square {p a b f left right : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> Cont BHist.Empty f left ->
      Cont f BHist.Empty right ->
        CategoryHomCarrier (append p a) (append p b) left ∧
          CategoryHomCarrier (append p a) (append p b) right ∧ hsame left right := by
  intro prefixCarrier homCarrier leftRel rightRel
  have leftSame : hsame left f := cont_left_unit_result leftRel
  have rightSame : hsame right f := cont_deterministic rightRel (cont_right_unit f)
  have leftCarrier : CategoryHomCarrier a b left := by
    cases leftSame
    exact homCarrier
  have rightCarrier : CategoryHomCarrier a b right := by
    cases rightSame
    exact homCarrier
  exact
    And.intro
      (FunctorPrefixHomCarrier_preserves prefixCarrier leftCarrier)
      (And.intro
        (FunctorPrefixHomCarrier_preserves prefixCarrier rightCarrier)
        (leftSame.trans rightSame.symm))

end BEDC.Derived.NatTransUp
