import BEDC.FKernel.Unary.Certificates

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Cont

local instance : AskSetup := MinimalAskSetup
local instance : PackageSetup := MinimalPackageSetup
local instance : NameCertSetup := MinimalNameCertSetup

def EoneCongruenceObligation : Prop :=
  ∀ {u v : BHist}, hsame u v → hsame (.e1 u) (.e1 v)

theorem EOneCongruenceObligation_holds : EOneCongruenceObligation := by
  intro u v same
  exact hsame_e1_congr same

theorem unary_append_e1_left :
    ∀ {h k : BHist}, UnaryHistory h → append (.e1 k) h = .e1 (append k h) := by
  intro h k uh
  induction h generalizing k with
  | Empty =>
      rfl
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      exact congrArg BHist.e1 (ih uh)

theorem unary_append_comm_left_induction :
    ∀ {h k : BHist}, UnaryHistory h → UnaryHistory k → append h k = append k h := by
  intro h k uh uk
  induction h generalizing k with
  | Empty =>
      exact append_empty_left k
  | e0 _ _ =>
      cases uh
  | e1 h ih =>
      exact (unary_append_e1_left (h := k) (k := h) uk).trans (congrArg BHist.e1 (ih uh uk))

theorem unary_append_comm :
    ∀ {h k : BHist}, UnaryHistory h → UnaryHistory k → append h k = append k h := by
  intro h k uh uk
  induction k generalizing h with
  | Empty =>
      exact cont_left_unit h
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact (congrArg BHist.e1 (ih uh uk)).trans (unary_append_e1_left (h := h) (k := k) uh).symm

theorem unary_append_comm_right_induction :
    ∀ {h k : BHist}, UnaryHistory h → UnaryHistory k → append h k = append k h := by
  intro h k uh uk
  induction k generalizing h with
  | Empty =>
      exact cont_left_unit h
  | e0 _ _ =>
      cases uk
  | e1 k ih =>
      exact (congrArg BHist.e1 (ih uh uk)).trans
        (unary_append_e1_left (h := h) (k := k) uh).symm

theorem unary_append_comm_hsame :
    ∀ {h k : BHist}, UnaryHistory h → UnaryHistory k → hsame (append h k) (append k h) := by
  intro h k uh uk
  induction k generalizing h with
  | Empty =>
      exact cont_left_unit h
  | e0 _ _ =>
      cases uk
  | e1 k ih =>
      exact (hsame_e1_congr (ih uh uk)).trans
        (unary_append_e1_left (h := h) (k := k) uh).symm

theorem unary_cont_comm {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact hr.trans ((unary_append_comm uh uk).trans hr'.symm)

theorem unary_continuation_commutativity {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' -> hsame r r' := by
  intro uh uk hr hr'
  exact unary_cont_comm uh uk hr hr'

theorem unary_cont_comm_from_append_comm {h k r r' : BHist} :
    append h k = append k h → Cont h k r → Cont k h r' → hsame r r' := by
  intro hcomm hr hr'
  cases hr
  cases hr'
  exact hcomm

theorem unary_cont_comm_obligation_holds : UnaryContinuationCommutativityObligation := by
  intro h k r r2 uh uk hr hr2
  exact unary_cont_comm uh uk hr hr2

theorem add_up_commutative_certificate_upgrade {h k r rprime : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h rprime →
      NameCert AddName ∧ Nonempty StabilityCert ∧ hsame r rprime := by
  intro uh uk hr hrprime
  constructor
  · exact add_up_name_certificate
  · constructor
    · exact nameCert_stability_witness_from_cert add_up_name_certificate
    · exact unary_cont_comm uh uk hr hrprime

theorem unary_continuation_associativity {a b c ab bc abc abc' : BHist} :
    UnaryHistory a → UnaryHistory b → UnaryHistory c →
    Cont a b ab → Cont b c bc → Cont ab c abc → Cont a bc abc' →
    hsame abc abc' := by
  intro _ _ _ hab hbc habc habc'
  cases hab
  cases hbc
  cases habc
  cases habc'
  exact append_assoc a b c

theorem add_up_interface_seed_with_units :
    Nonempty (NameCert AddName) ∧
      (∀ {h left right : BHist},
        UnaryHistory h → Cont h BHist.Empty left → Cont BHist.Empty h right →
          UnaryHistory left ∧ UnaryHistory right ∧ hsame left h ∧ hsame right h) ∧
      (∀ {a b c ab bc abc abc' : BHist},
        UnaryHistory a → UnaryHistory b → UnaryHistory c →
          Cont a b ab → Cont b c bc → Cont ab c abc → Cont a bc abc' →
            hsame abc abc') := by
  constructor
  · exact add_up_name_certificate_exists
  · constructor
    · intro h left right uh hleft hright
      exact unary_cont_unit uh hleft hright
    · intro a b c ab bc abc abc' ua ub uc hab hbc habc habc'
      exact unary_continuation_associativity ua ub uc hab hbc habc habc'

theorem unary_cont_assoc_with_closure {a b c ab bc abc abc' : BHist} :
    UnaryHistory a → UnaryHistory b → UnaryHistory c →
    Cont a b ab → Cont b c bc → Cont ab c abc → Cont a bc abc' →
    UnaryHistory ab ∧ UnaryHistory bc ∧ hsame abc abc' := by
  intro ua ub uc hab hbc habc habc'
  constructor
  · exact unary_cont_closed ua ub hab
  · constructor
    · exact unary_cont_closed ub uc hbc
    · exact unary_continuation_associativity ua ub uc hab hbc habc habc'

theorem comm_from_obligations
    (shift :
      ∀ {k h r : BHist}, UnaryHistory k → Cont k (.e1 h) r →
        ∃ v : BHist, Cont k h v ∧ hsame r (.e1 v))
    (eoneCong : ∀ {u v : BHist}, hsame u v → hsame (.e1 u) (.e1 v))
    {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  induction h generalizing k r r' with
  | Empty =>
      cases hr
      cases hr'
      exact (cont_left_unit k).symm
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      have left :
          hsame r (.e1 (append h k)) := by
        cases hr
        exact unary_append_e1_left (h := k) (k := h) uk
      cases shift uk hr' with
      | intro v shifted =>
          cases shifted with
          | intro hv sameRight =>
              have inner : hsame (append h k) v := ih uh uk rfl hv
              exact left.trans ((eoneCong inner).trans sameRight.symm)

theorem unary_commutativity_concrete
    (rightShift : forall {k h r' : BHist}, UnaryHistory k -> Cont k (.e1 h) r' -> exists v : BHist, Cont k h v ∧ hsame r' (.e1 v))
    {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' -> hsame r r' := by
  intro uh uk hr hr'
  exact comm_from_obligations rightShift (fun same => hsame_e1_congr same) uh uk hr hr'

theorem unary_commutativity_concrete_from_shift
    (rightShift :
      ∀ {k h r' : BHist}, UnaryHistory k → Cont k (.e1 h) r' →
        ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v))
    {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact comm_from_obligations rightShift (fun same => hsame_e1_congr same) uh uk hr hr'

theorem unary_shift_step {k0 h r' : BHist} :
    UnaryHistory k0 →
      (∀ {r : BHist}, Cont k0 (.e1 h) r →
        ∃ v : BHist, Cont k0 h v ∧ hsame r (.e1 v)) →
      Cont (.e1 k0) (.e1 h) r' →
      ∃ v : BHist, Cont (.e1 k0) h v ∧ hsame r' (.e1 v) := by
  intro _ _ hr'
  exact ⟨append (.e1 k0) h, rfl, hr'⟩

theorem unary_shift_step_with_unary_result {k0 h r' : BHist} :
    UnaryHistory k0 → UnaryHistory h →
      (forall {r : BHist}, Cont k0 (BHist.e1 h) r ->
        exists v : BHist, Cont k0 h v /\ hsame r (BHist.e1 v)) →
      Cont (BHist.e1 k0) (BHist.e1 h) r' →
      exists v : BHist,
        Cont (BHist.e1 k0) h v /\ hsame r' (BHist.e1 v) /\ UnaryHistory v := by
  intro uk uh shift hr'
  cases unary_shift_step uk shift hr' with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          exact ⟨v, hv, same, unary_cont_closed (unary_e1_closed uk) uh hv⟩

theorem unary_shift_base {h r : BHist} :
    Cont .Empty (.e1 h) r -> exists v : BHist, Cont .Empty h v /\ hsame r (.e1 v) := by
  intro hr
  exact ⟨h, cont_left_unit h, hr.trans (cont_left_unit (.e1 h)).symm⟩

theorem unary_shift_witness {k h r' : BHist} :
    UnaryHistory k → Cont k (.e1 h) r' →
      ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v) := by
  intro uk hr
  induction k generalizing h r' with
  | Empty =>
      exact unary_shift_base hr
  | e0 _ _ =>
      cases uk
  | e1 k ih =>
      exact unary_shift_step uk (by
        intro r hshift
        exact ih uk hshift) hr

theorem unary_shift_witness_with_factor {k h r' : BHist} :
    UnaryHistory k → UnaryHistory h → Cont k (.e1 h) r' →
      exists v : BHist, Cont k h v /\ hsame r' (.e1 v) /\ UnaryHistory v := by
  intro uk uh hr
  cases unary_shift_witness uk hr with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          exact ⟨v, hv, same, unary_cont_closed uk uh hv⟩

theorem unary_shift_result_closed {k h r' : BHist} :
    UnaryHistory k → UnaryHistory h → Cont k (.e1 h) r' → UnaryHistory r' := by
  intro uk uh hr
  cases unary_shift_witness_with_factor uk uh hr with
  | intro v shifted =>
      cases shifted with
      | intro _ shiftedTail =>
          cases shiftedTail with
          | intro same uv =>
              exact unary_transport (unary_e1_closed uv) (hsame_symm same)

theorem unary_right_shift_obligation_holds :
    (∀ {k h r' : BHist}, UnaryHistory k → Cont k (.e1 h) r' → ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v)) := by
  intro k h r' uk hr
  exact unary_shift_witness uk hr

theorem unary_shift_witness_obligation_pair :
    (∀ {k h r' : BHist},
      UnaryHistory k → Cont k (.e1 h) r' → ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v)) ∧
      UnaryRightShiftObligation := by
  exact And.intro unary_shift_witness unary_right_shift_obligation_holds

theorem unary_commutativity_refined {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact unary_cont_comm uh uk hr hr'

theorem unary_commutativity_concrete_direct {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact comm_from_obligations unary_shift_witness (fun same => hsame_e1_congr same) uh uk hr hr'

theorem unary_commutativity_concrete_with_closed_results {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' →
      hsame r r' ∧ UnaryHistory r ∧ UnaryHistory r' := by
  intro uh uk hr hr'
  constructor
  · exact unary_commutativity_concrete_direct uh uk hr hr'
  · constructor
    · exact unary_cont_closed uh uk hr
    · exact unary_cont_closed uk uh hr'

theorem unary_commutativity_concrete_induction {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  induction h generalizing k r r' with
  | Empty =>
      cases hr
      cases hr'
      exact (cont_left_unit k).symm
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      have left : hsame r (.e1 (append h k)) := by
        cases hr
        exact unary_append_e1_left (h := k) (k := h) uk
      cases unary_shift_witness uk hr' with
      | intro v shifted =>
          cases shifted with
          | intro hv sameRight =>
              have inner : hsame (append h k) v := ih uh uk rfl hv
              exact left.trans ((hsame_e1_congr inner).trans sameRight.symm)

theorem unary_commutativity_from_shift_induction
    (rightShift :
      ∀ {k h r' : BHist}, UnaryHistory k → Cont k (.e1 h) r' →
        ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v))
    {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  induction h generalizing k r r' with
  | Empty =>
      cases hr
      cases hr'
      exact (cont_left_unit k).symm
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      have left : hsame r (.e1 (append h k)) := by
        cases hr
        exact unary_append_e1_left (h := k) (k := h) uk
      cases rightShift uk hr' with
      | intro v shifted =>
          cases shifted with
          | intro hv sameRight =>
              have inner : hsame (append h k) v := ih uh uk rfl hv
              exact left.trans ((hsame_e1_congr inner).trans sameRight.symm)

theorem unary_commutativity_concrete_from_shift_witness
    (rightShift : forall {k h r' : BHist}, UnaryHistory k -> Cont k (.e1 h) r' ->
      exists v : BHist, Cont k h v ∧ hsame r' (.e1 v))
    {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' -> hsame r r' := by
  intro uh uk hr hr'
  exact unary_commutativity_from_shift_induction rightShift uh uk hr hr'

theorem unary_commutativity_concrete_obligation {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  induction h generalizing k r r' with
  | Empty =>
      cases hr
      cases hr'
      exact (cont_left_unit k).symm
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      have left : hsame r (.e1 (append h k)) := by
        cases hr
        exact unary_append_e1_left (h := k) (k := h) uk
      cases unary_shift_witness uk hr' with
      | intro v shifted =>
          cases shifted with
          | intro hv sameRight =>
              have inner : hsame (append h k) v := ih uh uk rfl hv
              exact left.trans ((hsame_e1_congr inner).trans sameRight.symm)

theorem unary_commutativity_obligation_induction {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact unary_commutativity_from_shift_induction unary_shift_witness uh uk hr hr'

theorem unary_commutativity_concrete_explicit_induction {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  induction h generalizing k r r' with
  | Empty =>
      cases hr
      cases hr'
      exact (cont_left_unit k).symm
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      have left : hsame r (.e1 (append h k)) := by
        cases hr
        exact unary_append_e1_left (h := k) (k := h) uk
      cases unary_shift_witness uk hr' with
      | intro v shifted =>
          cases shifted with
          | intro hv sameRight =>
              have inner : hsame (append h k) v := ih uh uk rfl hv
              exact left.trans ((hsame_e1_congr inner).trans sameRight.symm)

theorem unary_add_activation {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' -> hsame r r' := by
  intro uh uk hr hr'
  exact unary_commutativity_refined uh uk hr hr'

theorem add_up_commutative_license {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' ->
      hsame r r' /\ Nonempty (NameCert AddName) := by
  intro uh uk hr hr'
  constructor
  · exact unary_add_activation uh uk hr hr'
  · exact add_up_name_certificate_exists

theorem unary_comm_from_obligations
    (rightShift : ∀ {k h r' : BHist}, UnaryHistory k → Cont k (.e1 h) r' → ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v))
    (e1Cong : ∀ {u v : BHist}, hsame u v → hsame (.e1 u) (.e1 v))
    {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  have _rightShift :
      ∀ {k h r' : BHist}, UnaryHistory k → Cont k (.e1 h) r' → ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v) :=
    rightShift
  have _e1Cong : ∀ {u v : BHist}, hsame u v → hsame (.e1 u) (.e1 v) :=
    e1Cong
  exact unary_commutativity_refined uh uk hr hr'

theorem unary_shift {k h r' : BHist} :
    UnaryHistory k → Cont k (.e1 h) r' →
      ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v) := by
  intro _ hr'
  exact ⟨append k h, rfl, hr'⟩

theorem add_up_seed_from_unary_continuation :
    NameCert AddName /\
      (forall {h left right : BHist},
        UnaryHistory h -> Cont h BHist.Empty left -> Cont BHist.Empty h right ->
          UnaryHistory left /\ UnaryHistory right /\ hsame left h /\ hsame right h) /\
        (forall {a b c ab bc abc abc2 : BHist},
          UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
            Cont a b ab -> Cont b c bc -> Cont ab c abc -> Cont a bc abc2 ->
              hsame abc abc2) := by
  constructor
  · exact add_up_name_certificate
  · constructor
    · intro h left right uh hleft hright
      exact unary_cont_unit uh hleft hright
    · intro a b c ab bc abc abc2 ua ub uc hab hbc habc habc2
      exact unary_continuation_associativity ua ub uc hab hbc habc habc2

end BEDC.FKernel.Unary
