import BEDC.Derived.FunctorUp
import BEDC.Derived.CategoryUp

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

def NatTransPrefixComponentCarrier (p q a eta : BHist) : Prop :=
  UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧
    CategoryHomCarrier (append p a) (append q a) eta

theorem NatTransPrefixComponentCarrier_vert_comp_closed {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta composite -> NatTransPrefixComponentCarrier p r a composite := by
  intro left right comp
  cases left with
  | intro sourceCarrier leftRest =>
      cases leftRest with
      | intro _middleCarrier leftRest =>
          cases leftRest with
          | intro objectCarrier leftComponent =>
              cases right with
              | intro _middleCarrierAgain rightRest =>
                  cases rightRest with
                  | intro targetCarrier rightRest =>
                      cases rightRest with
                      | intro _objectCarrierAgain rightComponent =>
                          exact
                            And.intro sourceCarrier
                              (And.intro targetCarrier
                                (And.intro objectCarrier
                                  (CategoryHomCarrier_comp_closed leftComponent rightComponent comp)))

theorem NatTransPrefixIdentity_identity_component_square_closed {p a id left right : BHist} :
    UnaryHistory p -> UnaryHistory a -> Cont BHist.Empty BHist.Empty id ->
      Cont id BHist.Empty left -> Cont BHist.Empty id right ->
        CategoryHomCarrier (append p a) (append p a) left ∧
          CategoryHomCarrier (append p a) (append p a) right ∧ hsame left right := by
  intro prefixCarrier sourceCarrier idRel leftRel rightRel
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
  exact And.intro leftCarrier (And.intro rightCarrier (leftSame.trans rightSame.symm))

end BEDC.Derived.NatTransUp
