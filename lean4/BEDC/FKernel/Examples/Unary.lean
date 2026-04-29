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

theorem unary_transport {h k : BHist} : UnaryHistory h -> hsame h k -> UnaryHistory k := by
  intro uh hhk
  cases hhk
  exact uh

theorem unary_no_zero_extension {h : BHist} : UnaryHistory (.e0 h) -> False := by
  intro uh
  exact uh

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

theorem nat_up_name_certificate_exists : Nonempty (NameCert UnaryName) := by
  exact Nonempty.intro {
    sourceSpec := ()
    patternSpec := ()
    classifierSpec := ()
    stabilityCert := ()
    ledgerPolicy := ()
  }

theorem unary_addition_seed : True := True.intro

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

theorem unary_commutativity_refined {h k r r' : BHist} :
    UnaryHistory h → UnaryHistory k → Cont h k r → Cont k h r' → hsame r r' := by
  intro uh uk hr hr'
  exact unary_cont_comm uh uk hr hr'

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
