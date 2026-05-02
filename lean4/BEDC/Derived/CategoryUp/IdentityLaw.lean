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

end BEDC.Derived.CategoryUp
