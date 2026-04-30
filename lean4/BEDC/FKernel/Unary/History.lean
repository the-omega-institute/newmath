import BEDC.FKernel.Cont

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def UnaryHistory : BHist → Prop
  | .Empty => True
  | .e1 h => UnaryHistory h
  | .e0 _ => False

def UnaryRightShiftObligation : Prop :=
  forall {k h r : BHist}, UnaryHistory k -> Cont k (BHist.e1 h) r ->
    exists v : BHist, Cont k h v /\ hsame r (BHist.e1 v)

def UnaryContinuationCommutativityObligation : Prop :=
  forall {h k r r2 : BHist},
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r2 -> hsame r r2

theorem unary_empty : UnaryHistory BHist.Empty := by
  exact True.intro

def UnaryCont (h k r : BHist) : Prop :=
  UnaryHistory h ∧ UnaryHistory k ∧ Cont h k r

theorem unary_history_cases {h : BHist} :
    UnaryHistory h -> h = BHist.Empty \/ exists k : BHist, h = BHist.e1 k /\ UnaryHistory k := by
  intro uh
  cases h with
  | Empty =>
      exact Or.inl rfl
  | e0 h =>
      cases uh
  | e1 h =>
      exact Or.inr ⟨h, rfl, uh⟩

theorem unary_e1_closed {h : BHist} : UnaryHistory h -> UnaryHistory (.e1 h) := by
  intro uh
  exact uh

theorem unary_e1_inversion {h : BHist} : UnaryHistory (BHist.e1 h) -> UnaryHistory h := by
  intro uh
  exact uh

theorem unary_history_induction {P : BHist → Prop} :
    P BHist.Empty →
      (∀ h : BHist, UnaryHistory h → P h → P (BHist.e1 h)) →
      ∀ h : BHist, UnaryHistory h → P h := by
  intro base step h uh
  induction h with
  | Empty =>
      exact base
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      exact step h uh (ih uh)

theorem unary_transport {h k : BHist} : UnaryHistory h -> hsame h k -> UnaryHistory k := by
  intro uh hhk
  cases hhk
  exact uh

theorem unary_no_zero_extension {h : BHist} : UnaryHistory (.e0 h) -> False := by
  intro uh
  exact uh

theorem unary_history_judgment_generators :
    And (UnaryHistory BHist.Empty)
      (And
        (forall h : BHist, UnaryHistory h -> UnaryHistory (BHist.e1 h))
        (forall h : BHist, UnaryHistory (BHist.e0 h) -> False)) := by
  constructor
  · exact unary_empty
  · constructor
    · intro h uh
      exact unary_e1_closed uh
    · intro h uh
      exact unary_no_zero_extension uh

theorem unary_stability_certificate_fields :
    UnaryHistory BHist.Empty /\
      (forall h : BHist, UnaryHistory h -> UnaryHistory (.e1 h)) /\
        (forall h : BHist, UnaryHistory (.e0 h) -> False) := by
  constructor
  · exact unary_empty
  · constructor
    · intro h uh
      exact unary_e1_closed uh
    · intro h uh
      exact unary_no_zero_extension uh

theorem unary_stability_certificate_no_zero_projection {h : BHist} :
    UnaryHistory (BHist.e0 h) -> False := by
  intro uh
  exact unary_no_zero_extension uh

theorem unary_append_closed : ∀ {h k : BHist}, UnaryHistory h -> UnaryHistory k -> UnaryHistory (append h k) := by
  intro h k uh uk
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact ih uh uk

theorem unary_cont_closed {h k r : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r := by
  intro uh uk hr
  cases hr
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact ih uh uk

theorem unary_cont_preserves_unary_by_induction {h k r : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → UnaryHistory r := by
  intro uh uk hr
  cases hr
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact ih uh uk

theorem unary_cont_result_closed {h k r : BHist} :
    UnaryHistory h ∧ UnaryHistory k ∧ Cont h k r → UnaryHistory r := by
  intro packed
  cases packed with
  | intro uh rest =>
      cases rest with
      | intro uk hr =>
          exact unary_cont_closed uh uk hr

theorem unary_continuation_closure {h k r : BHist} :
    UnaryCont h k r → UnaryHistory r := by
  intro packed
  cases packed with
  | intro uh rest =>
      cases rest with
      | intro uk hr =>
          exact unary_cont_closed uh uk hr

theorem unary_repetition_continuation_closed {h k r : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r := by
  intro uh uk hr
  cases hr
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact ih uh uk

theorem unary_repetition_closed_under_continuation_seed {h k r : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → UnaryHistory r := by
  intro uh uk hr
  cases hr
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact ih uh uk

theorem unary_cont_right_factor {h k r : BHist} :
    Cont h k r → UnaryHistory r → UnaryHistory k := by
  intro hr ur
  cases hr
  induction k generalizing h with
  | Empty =>
      exact True.intro
  | e0 k ih =>
      cases ur
  | e1 k ih =>
      exact ih ur

theorem unary_cont_left_factor {h k r : BHist} :
    Cont h k r -> UnaryHistory r -> UnaryHistory h := by
  intro hr ur
  cases hr
  induction k generalizing h with
  | Empty =>
      exact ur
  | e0 k ih =>
      cases ur
  | e1 k ih =>
      exact ih ur

theorem unary_cont_factors_from_result {h k r : BHist} :
    Cont h k r -> UnaryHistory r -> UnaryHistory h ∧ UnaryHistory k := by
  intro hr ur
  constructor
  · exact unary_cont_left_factor hr ur
  · exact unary_cont_right_factor hr ur

theorem unary_cont_result_iff_factors {h k r : BHist} :
    Cont h k r -> (UnaryHistory r <-> UnaryHistory h /\ UnaryHistory k) := by
  intro hr
  constructor
  · intro ur
    exact unary_cont_factors_from_result hr ur
  · intro factors
    cases factors with
    | intro uh uk =>
        exact unary_cont_closed uh uk hr

theorem unary_continuation_closed_and_factors {h k r : BHist} :
    UnaryCont h k r ->
      UnaryHistory r /\ (Cont h k r -> UnaryHistory r -> UnaryHistory h /\ UnaryHistory k) := by
  intro cont
  constructor
  · exact unary_cont_result_closed cont
  · intro hr ur
    constructor
    · exact unary_cont_left_factor hr ur
    · exact unary_cont_right_factor hr ur

theorem unary_cont_unit {h left right : BHist} :
    UnaryHistory h -> Cont h BHist.Empty left -> Cont BHist.Empty h right ->
      UnaryHistory left ∧ UnaryHistory right ∧ hsame left h ∧ hsame right h := by
  intro uh hleft hright
  have leftSame : hsame left h := cont_deterministic hleft (cont_right_unit h)
  have rightSame : hsame right h := cont_deterministic hright (cont_left_unit h)
  constructor
  · exact unary_transport uh (hsame_symm leftSame)
  · constructor
    · exact unary_transport uh (hsame_symm rightSame)
    · constructor
      · exact leftSame
      · exact rightSame


end BEDC.FKernel.Unary
