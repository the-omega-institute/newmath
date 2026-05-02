import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_two_sided_identity_law {a b f left right : BHist} :
    CategoryHomCarrier a b f -> Cont BHist.Empty f left -> Cont f BHist.Empty right ->
      CategoryHomCarrier a b left ∧ CategoryHomCarrier a b right ∧ hsame left f ∧
        hsame right f ∧ hsame left right := by
  intro homCarrier leftRel rightRel
  have leftSame : hsame left f := cont_left_unit_result leftRel
  have rightSame : hsame right f := cont_deterministic rightRel (cont_right_unit f)
  have leftCarrier : CategoryHomCarrier a b left := by
    cases leftSame
    exact homCarrier
  have rightCarrier : CategoryHomCarrier a b right := by
    cases rightSame
    exact homCarrier
  exact And.intro leftCarrier
    (And.intro rightCarrier
      (And.intro leftSame (And.intro rightSame (leftSame.trans rightSame.symm))))

theorem CategoryHomCarrier_left_identity_carrier_result {a b id f left : BHist} :
    CategoryHomCarrier a a id -> CategoryHomCarrier a b f -> Cont id f left ->
      CategoryHomCarrier a b left ∧ hsame left f := by
  intro identityCarrier homCarrier leftRel
  have emptyIdentity : CategoryHomCarrier a a BHist.Empty :=
    CategoryHomCarrier_empty_identity identityCarrier.left
  have idEmpty : hsame id BHist.Empty :=
    CategoryHomCarrier_morphism_deterministic identityCarrier emptyIdentity
  cases idEmpty
  have leftSame : hsame left f :=
    cont_left_unit_result leftRel
  have leftCarrier : CategoryHomCarrier a b left := by
    cases leftSame
    exact homCarrier
  exact And.intro leftCarrier leftSame

theorem CategoryHomCarrier_right_identity_carrier_result {a b id f right : BHist} :
    CategoryHomCarrier b b id -> CategoryHomCarrier a b f -> Cont f id right ->
      CategoryHomCarrier a b right ∧ hsame right f := by
  intro identityCarrier homCarrier rightRel
  have emptyIdentity : CategoryHomCarrier b b BHist.Empty :=
    CategoryHomCarrier_empty_identity identityCarrier.left
  have idEmpty : hsame id BHist.Empty :=
    CategoryHomCarrier_morphism_deterministic identityCarrier emptyIdentity
  cases idEmpty
  have rightSame : hsame right f :=
    cont_deterministic rightRel (cont_right_unit f)
  have rightCarrier : CategoryHomCarrier a b right := by
    cases rightSame
    exact homCarrier
  exact And.intro rightCarrier rightSame

theorem CategoryHomCarrier_comp_left_right_identity_result {a b idA idB f left both : BHist} :
    CategoryHomCarrier a a idA -> CategoryHomCarrier b b idB -> CategoryHomCarrier a b f ->
      Cont idA f left -> Cont left idB both -> CategoryHomCarrier a b both ∧ hsame both f := by
  intro leftIdentity rightIdentity homCarrier leftRel rightRel
  have leftResult :
      CategoryHomCarrier a b left ∧ hsame left f :=
    CategoryHomCarrier_left_identity_carrier_result leftIdentity homCarrier leftRel
  have bothResult :
      CategoryHomCarrier a b both ∧ hsame both left :=
    CategoryHomCarrier_right_identity_carrier_result rightIdentity leftResult.left rightRel
  exact And.intro bothResult.left (hsame_trans bothResult.right leftResult.right)

end BEDC.Derived.CategoryUp
