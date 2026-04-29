import BEDC.FKernel.Package

/-! Gap ledgers record which admitted histories fall under visible package tokens. -/
namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

class DomainSetup where
  Domain : Type
  InDom : Domain → BHist → Prop

variable [AskSetup] [PackageSetup] [G : DomainSetup]

abbrev Domain : Type := G.Domain
abbrev InDom : Domain → BHist → Prop := G.InDom

structure DomainPolicy (D : Domain) : Prop where
  transport : ∀ {h k : BHist}, InDom D h → hsame h k → InDom D k

def InGapSig (bundle : ProbeBundle ProbeName) (D : Domain) (p : Pkg) (h : BHist) : Prop :=
  InDom D h ∧ ∃ s : BHist, SigRel bundle h s ∧ TokIntro bundle s p

structure GapPolicy (bundle : ProbeBundle ProbeName) (D : Domain) : Prop where
  generation : ∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h → ∃ s : BHist, TokIntro bundle s p
  coverage : ∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h
  separation : ∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q

theorem gap_coverage :
    ∀ {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist},
      GapPolicy bundle D → InDom D h → ∃ p : Pkg, InGapSig bundle D p h := by
  intro bundle D h hgap hh
  exact hgap.coverage hh

theorem gap_separation :
    ∀ {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg},
      GapPolicy bundle D → InDom D h → InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q := by
  intro bundle D h p q hgap hh hp hq
  exact hgap.separation hh hp hq

theorem policy_gap_separation
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → PackageTokenPolicy bundle →
      InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q := by
  intro askPolicy packagePolicy hp hq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro hIn hpSig =>
      cases hq with
      | intro _ hqSig =>
          cases hpSig with
          | intro s hsData =>
              cases hqSig with
              | intro t htData =>
                  cases hsData with
                  | intro hs hpTok =>
                      cases htData with
                      | intro ht hqTok =>
                          have hst : hsame s t :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D) (h := h) (s := s) (t := t)
                              askPolicy hIn hs ht
                          exact packagePolicy.soundness hpTok hqTok hst

omit [AskSetup] [PackageSetup] in
theorem domain_transport {D : Domain} (policy : DomainPolicy D) {h k : BHist} :
    InDom D h → hsame h k → InDom D k := by
  intro hh hhk
  exact policy.transport hh hhk

omit [AskSetup] [PackageSetup] G in
theorem compGap_coverage : True := True.intro

def MinimalDomainSetup : DomainSetup where
  Domain := Unit
  InDom := fun _ _ => True

end BEDC.FKernel.Gap
