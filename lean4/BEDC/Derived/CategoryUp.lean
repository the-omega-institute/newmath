import BEDC.FKernel.Unary
import BEDC.FKernel.Cont

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CategoryHomCarrier (a b f : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory f ∧ Cont a f b

theorem CategoryHomCarrier_empty_identity {h : BHist} :
    UnaryHistory h -> CategoryHomCarrier h h BHist.Empty := by
  intro carrier
  exact And.intro carrier (And.intro carrier (And.intro unary_empty (cont_right_unit h)))

theorem CategoryHomCarrier_comp_closed {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a c fg := by
  intro left right comp
  cases left with
  | intro sourceCarrier leftRest =>
      cases leftRest with
      | intro _middleCarrier leftHomRest =>
          cases leftHomRest with
          | intro fCarrier leftCont =>
              cases right with
              | intro middleCarrier rightRest =>
                  cases rightRest with
                  | intro targetCarrier rightHomRest =>
                      cases rightHomRest with
                      | intro gCarrier rightCont =>
                          cases leftCont
                          cases rightCont
                          cases comp
                          exact
                            And.intro sourceCarrier
                              (And.intro targetCarrier
                                (And.intro
                                  (unary_cont_closed fCarrier gCarrier (cont_intro rfl))
                                  (cont_intro (append_assoc a f g))))

theorem CategoryHomCarrier_identity_square_closed {a b f left right : BHist} :
    CategoryHomCarrier a b f -> Cont BHist.Empty f left -> Cont f BHist.Empty right ->
      CategoryHomCarrier a b left ∧ CategoryHomCarrier a b right ∧ hsame left right := by
  intro homCarrier leftRel rightRel
  have leftSame : hsame left f := cont_left_unit_result leftRel
  have rightSame : hsame right f := cont_deterministic rightRel (cont_right_unit f)
  have leftCarrier : CategoryHomCarrier a b left := by
    cases leftSame
    exact homCarrier
  have rightCarrier : CategoryHomCarrier a b right := by
    cases rightSame
    exact homCarrier
  exact And.intro leftCarrier (And.intro rightCarrier (leftSame.trans rightSame.symm))

theorem CategoryHomCarrier_comp_assoc_closed {a b c d f g h fg gh left right : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier c d h ->
      Cont f g fg -> Cont g h gh -> Cont fg h left -> Cont f gh right ->
        CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧ hsame left right := by
  intro first second third fgRel ghRel leftRel rightRel
  have fgCarrier : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed first second fgRel
  have ghCarrier : CategoryHomCarrier b d gh :=
    CategoryHomCarrier_comp_closed second third ghRel
  exact
    And.intro
      (CategoryHomCarrier_comp_closed fgCarrier third leftRel)
      (And.intro
        (CategoryHomCarrier_comp_closed first ghCarrier rightRel)
        (cont_assoc_hsame fgRel leftRel ghRel rightRel))

theorem CategoryHomCarrier_morphism_deterministic {a b f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier a b g -> hsame f g := by
  intro left right
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _targetCarrier leftHomRest =>
          cases leftHomRest with
          | intro _fCarrier leftCont =>
              cases right with
              | intro _sourceCarrier' rightRest =>
                  cases rightRest with
                  | intro _targetCarrier' rightHomRest =>
                      cases rightHomRest with
                      | intro _gCarrier rightCont =>
                          exact cont_left_cancel leftCont rightCont

structure ContinuationMorphism (src tgt : BHist) where
  tail : BHist
  rel : Cont src tail tgt

theorem ContinuationMorphism_identity_comp_closure :
    (forall h : BHist, Nonempty (ContinuationMorphism h h)) ∧
      (forall {a b c : BHist}, ContinuationMorphism a b ->
        ContinuationMorphism b c -> Nonempty (ContinuationMorphism a c)) := by
  constructor
  · intro h
    exact Nonempty.intro { tail := BHist.Empty, rel := cont_right_unit h }
  · intro a b c left right
    cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            refine Nonempty.intro { tail := append leftTail rightTail, rel := ?_ }
            cases leftRel
            exact rightRel.trans (append_assoc a leftTail rightTail)

theorem category_cont_left_e0_result_cases {h k r : BHist} :
    Cont (BHist.e0 h) k (BHist.e0 r) ->
      (k = BHist.Empty ∧ hsame h r) ∨
        (∃ k0 : BHist, k = BHist.e0 k0 ∧ Cont (BHist.e0 h) k0 r) := by
  intro hcont
  cases k with
  | Empty =>
      left
      constructor
      · rfl
      · exact (BHist.e0.inj hcont).symm
  | e0 k0 =>
      right
      exact Exists.intro k0 (And.intro rfl (BHist.e0.inj hcont))
  | e1 k0 =>
      cases hcont

end BEDC.Derived.CategoryUp
