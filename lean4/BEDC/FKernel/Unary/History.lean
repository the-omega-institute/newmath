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

def EOneCongruenceObligation : Prop :=
  ∀ {u v : BHist}, hsame u v → hsame (.e1 u) (.e1 v)

theorem eone_congruence_obligation_holds : EOneCongruenceObligation := by
  intro u v h
  exact hsame_e1_congr h

def UnaryContinuationCommutativityObligation : Prop :=
  forall {h k r r2 : BHist},
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r2 -> hsame r r2

theorem unary_commutativity_obligation_iff :
    UnaryContinuationCommutativityObligation ↔
      (∀ {h k r r' : BHist}, UnaryHistory h → UnaryHistory k →
        Cont h k r → Cont k h r' → hsame r r') := by
  rfl

theorem UnaryContinuationCommutativityObligation_iff_fields :
    UnaryContinuationCommutativityObligation ↔
      (∀ {h k r r2 : BHist}, UnaryHistory h → UnaryHistory k →
        Cont h k r → Cont k h r2 → hsame r r2) := by
  rfl

theorem unary_empty : UnaryHistory BHist.Empty := by
  exact True.intro

def UnaryCont (h k r : BHist) : Prop :=
  UnaryHistory h ∧ UnaryHistory k ∧ Cont h k r

theorem UnaryCont_iff_fields {h k r : BHist} :
    UnaryCont h k r ↔ UnaryHistory h ∧ UnaryHistory k ∧ Cont h k r := by
  rfl

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

theorem unary_history_empty_or_e1_tail {h : BHist} :
    UnaryHistory h → h = BHist.Empty ∨ ∃ t : BHist, h = BHist.e1 t ∧ UnaryHistory t := by
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

theorem unary_closure_under_one_extension {h : BHist} :
    UnaryHistory h -> UnaryHistory (BHist.e1 h) := by
  intro uh
  exact uh

theorem unary_double_e1_closed {h : BHist} :
    UnaryHistory h -> UnaryHistory (BHist.e1 (BHist.e1 h)) := by
  intro uh
  exact unary_e1_closed (unary_e1_closed uh)

theorem unary_e1_inversion {h : BHist} : UnaryHistory (BHist.e1 h) -> UnaryHistory h := by
  intro uh
  exact uh

theorem unary_history_e1_iff {h : BHist} :
    UnaryHistory (BHist.e1 h) <-> UnaryHistory h := by
  rfl

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

theorem unary_histories_induction_from_generators {P : BHist -> Prop} :
    P BHist.Empty ->
      (forall h : BHist, UnaryHistory h -> P h -> P (BHist.e1 h)) ->
      forall h : BHist, UnaryHistory h -> P h := by
  intro base step h uh
  induction h with
  | Empty =>
      exact base
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      exact step h uh (ih uh)

theorem unary_histories_closed_generation {P : BHist → Prop} :
    P BHist.Empty →
      (∀ h : BHist, UnaryHistory h → P h → P (BHist.e1 h)) →
      (∀ h : BHist, UnaryHistory h → P h) ∧
        (∀ h : BHist, UnaryHistory (BHist.e0 h) → False) := by
  intro base step
  constructor
  · intro h uh
    induction h with
    | Empty =>
        exact base
    | e0 h ih =>
        cases uh
    | e1 h ih =>
        exact step h uh (ih uh)
  · intro h uh
    cases uh

theorem unary_history_closed_generation_spine {P : BHist -> Prop} :
    P BHist.Empty ->
      (forall h : BHist, UnaryHistory h -> P h -> P (BHist.e1 h)) ->
      (forall h : BHist, UnaryHistory h -> P h) /\
        (forall h : BHist, UnaryHistory (BHist.e0 h) -> False) := by
  exact unary_histories_closed_generation

theorem unary_transport {h k : BHist} : UnaryHistory h -> hsame h k -> UnaryHistory k := by
  intro uh hhk
  cases hhk
  exact uh

theorem unary_transport_symm {h k : BHist} : UnaryHistory k -> hsame h k -> UnaryHistory h := by
  intro uk hhk
  exact unary_transport uk (hsame_symm hhk)

theorem unary_history_hsame_iff {h k : BHist} :
    hsame h k → (UnaryHistory h ↔ UnaryHistory k) := by
  intro hhk
  exact Iff.intro
    (fun uh => unary_transport uh hhk)
    (fun uk => unary_transport_symm uk hhk)

theorem unary_no_zero_extension {h : BHist} : UnaryHistory (.e0 h) -> False := by
  intro uh
  exact uh

theorem unary_history_not_e0_head {h t : BHist} :
    UnaryHistory h -> h = BHist.e0 t -> False := by
  intro uh eq
  cases eq
  exact unary_no_zero_extension uh

theorem unary_history_e0_iff_false {h : BHist} : UnaryHistory (BHist.e0 h) ↔ False := by
  constructor
  · intro uh
    exact unary_no_zero_extension uh
  · intro impossible
    cases impossible

theorem unary_history_hsame_zero_absurd {h k : BHist} :
    UnaryHistory h -> hsame h (BHist.e0 k) -> False := by
  intro uh same
  cases same
  exact unary_no_zero_extension uh

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

theorem unary_history_judgment :
    UnaryHistory BHist.Empty /\
      (forall h : BHist, UnaryHistory h -> UnaryHistory (BHist.e1 h)) /\
      (forall h : BHist, UnaryHistory (BHist.e0 h) -> False) := by
  exact unary_history_judgment_generators

theorem unary_repetition_histories_generators :
    UnaryHistory BHist.Empty ∧
      (∀ h : BHist, UnaryHistory h → UnaryHistory (BHist.e1 h)) ∧
      (∀ h : BHist, UnaryHistory (BHist.e0 h) → False) := by
  exact unary_history_judgment_generators

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

theorem unary_stability_certificate_base_step_nozero_pair :
    UnaryHistory BHist.Empty ∧
      (forall h : BHist, UnaryHistory h -> UnaryHistory (BHist.e1 h)) ∧
        (forall h : BHist, UnaryHistory (BHist.e0 h) -> False) := by
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

theorem unary_append_closed_right_induction :
    ∀ {h k : BHist}, UnaryHistory h → UnaryHistory k → UnaryHistory (append h k) := by
  intro h k uh uk
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact ih uh uk

theorem unary_append_factors_iff_result {h k : BHist} :
    UnaryHistory h ∧ UnaryHistory k ↔ UnaryHistory (append h k) := by
  constructor
  · intro factors
    cases factors with
    | intro uh uk =>
        exact unary_append_closed uh uk
  · intro ur
    induction k generalizing h with
    | Empty =>
        constructor
        · exact ur
        · exact unary_empty
    | e0 k ih =>
        cases ur
    | e1 k ih =>
        exact ih ur

theorem unary_append_right_factor {h k : BHist} :
    UnaryHistory (append h k) → UnaryHistory k := by
  intro ur
  induction k generalizing h with
  | Empty =>
      exact unary_empty
  | e0 k ih =>
      cases ur
  | e1 k ih =>
      exact ih ur

theorem unary_append_left_factor {h k : BHist} :
    UnaryHistory (append h k) → UnaryHistory h := by
  intro ur
  induction k generalizing h with
  | Empty =>
      exact ur
  | e0 k ih =>
      cases ur
  | e1 k ih =>
      exact ih ur

theorem unary_append_e0_left_absurd :
    forall {h k : BHist}, UnaryHistory (append (BHist.e0 h) k) -> False := by
  intro h k uh
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      exact uh
  | e1 k ih =>
      exact ih uh

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

theorem unary_continuation_closure_up_to_hsame {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → hsame r r' → UnaryHistory r' := by
  intro uh uk hr same
  exact unary_transport (unary_cont_closed uh uk hr) same

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

theorem unary_continuation_closure_spine {h k r : BHist} :
    UnaryCont h k r → UnaryHistory r ∧ Cont h k r ∧ UnaryHistory h ∧ UnaryHistory k := by
  intro packed
  cases packed with
  | intro uh rest =>
      cases rest with
      | intro uk hr =>
          constructor
          · exact unary_cont_closed uh uk hr
          · constructor
            · exact hr
            · constructor
              · exact uh
              · exact uk

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

theorem unary_cont_factors_iff_result {h k r : BHist} :
    Cont h k r -> (UnaryHistory h ∧ UnaryHistory k ↔ UnaryHistory r) := by
  intro hr
  constructor
  · intro factors
    exact (unary_cont_result_iff_factors hr).mpr factors
  · intro ur
    exact (unary_cont_result_iff_factors hr).mp ur

theorem unary_cont_iff_result_unary {h k r : BHist} (hr : Cont h k r) :
    UnaryCont h k r ↔ UnaryHistory r := by
  constructor
  · intro cont
    exact unary_continuation_closure cont
  · intro ur
    have factors : UnaryHistory h ∧ UnaryHistory k := unary_cont_factors_from_result hr ur
    cases factors with
    | intro uh uk =>
        exact And.intro uh (And.intro uk hr)

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

theorem unary_repetition_continuation_closed_and_factors {h k r : BHist} :
    (UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r) ∧
      (Cont h k r -> UnaryHistory r -> UnaryHistory h ∧ UnaryHistory k) := by
  constructor
  · intro uh uk hr
    exact unary_repetition_continuation_closed uh uk hr
  · intro hr ur
    exact unary_cont_factors_from_result hr ur

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

theorem addition_like_unit_laws {h left right : BHist} :
    UnaryHistory h -> Cont BHist.Empty h left -> Cont h BHist.Empty right ->
      hsame left h /\ hsame right h := by
  intro _ hleft hright
  constructor
  · exact cont_deterministic hleft (cont_left_unit h)
  · exact cont_deterministic hright (cont_right_unit h)

theorem unary_cont_unit_same_pair {h left right : BHist} :
    UnaryHistory h → Cont h BHist.Empty left → Cont BHist.Empty h right →
      hsame left right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro uh hleft hright
  have packed := unary_cont_unit uh hleft hright
  cases packed with
  | intro leftUnary rest =>
      cases rest with
      | intro rightUnary sameRest =>
          cases sameRest with
          | intro leftSame rightSame =>
              constructor
              · exact hsame_trans leftSame (hsame_symm rightSame)
              · constructor
                · exact leftUnary
                · exact rightUnary

theorem unaryCont_empty_units_same {h left right : BHist} :
    UnaryCont h BHist.Empty left -> UnaryCont BHist.Empty h right -> hsame left right := by
  intro leftCont rightCont
  cases leftCont with
  | intro _ leftRest =>
      cases leftRest with
      | intro _ hleft =>
          cases rightCont with
          | intro _ rightRest =>
              cases rightRest with
              | intro _ hright =>
                  have leftSame : hsame left h :=
                    cont_deterministic hleft (cont_right_unit h)
                  have rightSame : hsame right h :=
                    cont_deterministic hright (cont_left_unit h)
                  exact hsame_trans leftSame (hsame_symm rightSame)

end BEDC.FKernel.Unary
