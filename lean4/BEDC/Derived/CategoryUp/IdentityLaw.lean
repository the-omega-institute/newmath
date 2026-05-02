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

theorem category_cont_left_right_identity_tail_result {a b idA f idB left both : BHist} :
    Cont a idA a -> Cont a f b -> Cont b idB b -> Cont idA f left ->
      Cont left idB both -> hsame both f := by
  intro leftIdentity morph rightIdentity leftRel rightRel
  have idAEmpty : hsame idA BHist.Empty :=
    cont_left_cancel leftIdentity (cont_right_unit a)
  have idBEmpty : hsame idB BHist.Empty :=
    cont_left_cancel rightIdentity (cont_right_unit b)
  have leftSame : hsame left f := by
    cases idAEmpty
    exact cont_left_unit_result leftRel
  have bothLeft : Cont f idB both := by
    cases leftSame
    exact rightRel
  cases idBEmpty
  exact cont_deterministic bothLeft (cont_right_unit f)

theorem CategoryHomCarrier_comp_middle_identity_result {a b c f id g fid result fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b b id -> CategoryHomCarrier b c g ->
      Cont f id fid -> Cont fid g result -> Cont f g fg ->
        CategoryHomCarrier a c result ∧ CategoryHomCarrier a c fg ∧ hsame result fg := by
  intro left identity right fidRel resultRel fgRel
  have fidResult :
      CategoryHomCarrier a b fid ∧ hsame fid f :=
    CategoryHomCarrier_right_identity_carrier_result identity left fidRel
  have resultCarrier : CategoryHomCarrier a c result :=
    CategoryHomCarrier_comp_closed fidResult.left right resultRel
  have fgCarrier : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right fgRel
  have sameResult : hsame result fg :=
    cont_respects_hsame fidResult.right (hsame_refl g) resultRel fgRel
  exact And.intro resultCarrier (And.intro fgCarrier sameResult)

theorem category_cont_middle_identity_tail_result {a b c f id g fid result fg : BHist} :
    Cont a f b -> Cont b id b -> Cont b g c -> Cont f id fid -> Cont fid g result ->
      Cont f g fg -> hsame result fg := by
  intro left identity right fidRel resultRel fgRel
  have idEmpty : hsame id BHist.Empty :=
    cont_left_cancel identity (cont_right_unit b)
  have fidSame : hsame fid f := by
    cases idEmpty
    exact cont_deterministic fidRel (cont_right_unit f)
  exact cont_respects_hsame fidSame (hsame_refl g) resultRel fgRel

theorem ContinuationMorphism_comp_middle_identity_tail_result {a b c : BHist}
    (left : ContinuationMorphism a b) (identity : ContinuationMorphism b b)
    (right : ContinuationMorphism b c) :
    hsame identity.tail BHist.Empty ∧
      hsame (ContinuationMorphism_comp_closed (ContinuationMorphism_comp_closed left identity) right).tail
        (ContinuationMorphism_comp_closed left right).tail := by
  constructor
  · cases identity with
    | mk identityTail identityRel =>
        exact cont_left_cancel identityRel (cont_right_unit b)
  · cases left with
    | mk leftTail leftRel =>
        cases identity with
        | mk identityTail identityRel =>
            cases right with
            | mk rightTail rightRel =>
                have identityTailEmptyLocal : hsame identityTail BHist.Empty :=
                  cont_left_cancel identityRel (cont_right_unit b)
                have collapsedMiddle : hsame (append leftTail identityTail) leftTail :=
                  hsame_trans (congrArg (append leftTail) identityTailEmptyLocal)
                    (append_empty_right leftTail)
                exact congrArg (fun tail => append tail rightTail) collapsedMiddle

theorem ContinuationMorphism_comp_left_right_identity_tail_result {a b : BHist}
    (leftId : ContinuationMorphism a a) (m : ContinuationMorphism a b)
    (rightId : ContinuationMorphism b b) :
    hsame leftId.tail BHist.Empty ∧ hsame rightId.tail BHist.Empty ∧
      hsame
        (ContinuationMorphism_comp_closed
          (ContinuationMorphism_comp_closed leftId m) rightId).tail
        m.tail := by
  constructor
  · cases leftId with
    | mk leftTail leftRel =>
        exact cont_left_cancel leftRel (cont_right_unit a)
  · constructor
    · cases rightId with
      | mk rightTail rightRel =>
          exact cont_left_cancel rightRel (cont_right_unit b)
    · cases leftId with
      | mk leftTail leftRel =>
          cases m with
          | mk morphTail morphRel =>
              cases rightId with
              | mk rightTail rightRel =>
                  have leftTailEmpty : hsame leftTail BHist.Empty :=
                    cont_left_cancel leftRel (cont_right_unit a)
                  have rightTailEmpty : hsame rightTail BHist.Empty :=
                    cont_left_cancel rightRel (cont_right_unit b)
                  cases leftTailEmpty
                  cases rightTailEmpty
                  exact hsame_trans
                    (congrArg (fun tail => append tail BHist.Empty) (append_empty_left morphTail))
                    (append_empty_right morphTail)

end BEDC.Derived.CategoryUp
