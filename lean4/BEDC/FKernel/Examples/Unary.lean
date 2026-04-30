import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont

/-! Placeholder unary-history example scaffolding for later concrete developments. -/
namespace BEDC.FKernel.Examples.Unary

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

def UnaryHistory : BHist → Prop
  | .Empty => True
  | .e1 h => UnaryHistory h
  | .e0 _ => False

def UnaryRightShiftObligation : Prop :=
  forall {k h r : BHist}, UnaryHistory k -> Cont k (BHist.e1 h) r ->
    exists v : BHist, Cont k h v /\ hsame r (BHist.e1 v)

def UnaryContinuationCommutativityObligation : Prop :=
  ∀ {h k r r' : BHist},
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r'

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

def UnaryDomainSetup : DomainSetup where
  Domain := Unit
  InDom := fun _ h => UnaryHistory h

local instance : DomainSetup := UnaryDomainSetup

theorem unary_domain_policy :
    @DomainPolicy (G := UnaryDomainSetup) (D := ()) where
  transport := by
    intro h k hh hsamehk
    cases hsamehk
    exact hh

def UnaryBundle : ProbeBundle ProbeName := .Bcons () .Bnil
def UnaryDomain : Domain := ()
def UnaryName : DerivedName := ()
def AddName : DerivedName := ()

theorem unary_domain_gap_transport {bundle : ProbeBundle ProbeName} {p : Pkg} {h k s : BHist} :
    InGapSig bundle UnaryDomain p h -> hsame h k -> BEDC.FKernel.Sig.SigRel bundle k s ->
      TokIntro bundle s p -> InGapSig bundle UnaryDomain p k := by
  intro hgap hhk hsig htok
  exact inGapSig_domain_transport_with_signature
    (bundle := bundle) (D := UnaryDomain) (p := p) (h := h) (k := k) (s := s)
    unary_domain_policy hgap hhk hsig htok

theorem nat_up_name_certificate : NameCert UnaryName := by
  exact NameCert.mk () () () () ()

theorem concrete_natup_namecert : NameCert UnaryName := by
  exact nat_up_name_certificate

theorem concrete_natup_namecert_primary : NameCert UnaryName := by
  exact NameCert.mk () () () () ()

theorem nat_up_name_certificate_witnesses :
    ∃ source : SourceSpec, ∃ pattern : PatternSpec, ∃ classifier : ClassifierSpec,
      ∃ stability : StabilityCert, ∃ ledger : LedgerPolicy, True := by
  have cert : NameCert UnaryName := nat_up_name_certificate
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact ⟨source, pattern, classifier, stability, ledger, True.intro⟩

theorem nat_up_name_certificate_exists : Nonempty (NameCert UnaryName) := by
  exact Nonempty.intro nat_up_name_certificate

theorem nat_up_licensed_not_primitive : NameCert UnaryName ∧ Nonempty (NameCert UnaryName) := by
  constructor
  · exact nat_up_name_certificate
  · exact nat_up_name_certificate_exists

theorem nat_up_seed_from_unary_continuation :
    NameCert UnaryName ∧
      (∀ {h k r : BHist},
        UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r) := by
  constructor
  · exact nat_up_name_certificate
  · intro h k r uh uk hr
    exact unary_cont_closed uh uk hr

theorem nat_up_interface_seed :
    UnaryHistory BHist.Empty ∧
      (∀ {h k r : BHist}, UnaryHistory h → UnaryHistory k → Cont h k r → UnaryHistory r) ∧
        Nonempty (NameCert UnaryName) := by
  constructor
  · exact unary_empty
  · constructor
    · intro h k r uh uk hr
      exact unary_repetition_closed_under_continuation_seed uh uk hr
    · exact Nonempty.intro nat_up_name_certificate

theorem nat_up_certificate_seed_not_primitive :
    NameCert UnaryName ∧ Nonempty (NameCert UnaryName) := by
  exact nat_up_licensed_not_primitive

theorem nat_up_certificate_source_witness : Nonempty SourceSpec := by
  exact nameCert_source_witness_from_cert nat_up_name_certificate

theorem nat_up_certificate_field_witnesses :
    Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec /\
      Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  exact nameCert_field_witnesses nat_up_name_certificate

theorem nat_up_certificate_has_ledger : Nonempty LedgerPolicy := by
  exact derived_interfaces_have_ledger nat_up_name_certificate

theorem nat_up_stability_witness : Nonempty StabilityCert := by
  exact Nonempty.intro ()

theorem nat_up_certificate_stability_and_ledger :
    Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  constructor
  · exact nat_up_stability_witness
  · exact nat_up_certificate_has_ledger

theorem add_up_name_certificate_exists : Nonempty (NameCert AddName) := by
  exact Nonempty.intro (NameCert.mk () () () () ())

theorem add_up_name_certificate : NameCert AddName := by
  exact NameCert.mk () () () () ()

theorem concrete_addup_namecert : NameCert AddName := by
  exact add_up_name_certificate

theorem add_up_licensed_not_primitive : NameCert AddName ∧ Nonempty (NameCert AddName) := by
  exact And.intro add_up_name_certificate add_up_name_certificate_exists

theorem add_up_certificate_field_witnesses :
    Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec /\
      Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  exact nameCert_field_witnesses add_up_name_certificate

theorem add_up_certificate_has_ledger : Nonempty LedgerPolicy := by
  exact derived_interfaces_have_ledger add_up_name_certificate

theorem unary_addition_seed : True := True.intro

theorem add_activation_stability_field (cert : NameCert UnaryName) : Nonempty StabilityCert := by
  cases cert with
  | mk _ _ _ stability _ =>
      exact Nonempty.intro stability

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

theorem unary_cont_comm {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact hr.trans ((unary_append_comm uh uk).trans hr'.symm)

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

theorem unary_right_shift_obligation_holds :
    (∀ {k h r' : BHist}, UnaryHistory k → Cont k (.e1 h) r' → ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v)) := by
  intro k h r' uk hr
  exact unary_shift_witness uk hr

theorem unary_commutativity_refined {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact unary_cont_comm uh uk hr hr'

theorem unary_commutativity_concrete_direct {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact comm_from_obligations unary_shift_witness (fun same => hsame_e1_congr same) uh uk hr hr'

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

end BEDC.FKernel.Examples.Unary
