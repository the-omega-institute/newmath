import BEDC.FKernel.Gap.Core

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

theorem policy_gap_separation_with_domain_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → InGapSig bundle D p h → InGapSig bundle D q h →
      ∃ s : BHist, ∃ t : BHist,
        InDom D h ∧ SigRel bundle h s ∧ SigRel bundle h t ∧
          TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t ∧ psame bundle p q := by
  intro policy hp hq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro hD hpWitness =>
      cases hq with
      | intro _ hqWitness =>
          cases hpWitness with
          | intro s hpData =>
              cases hqWitness with
              | intro t hqData =>
                  cases hpData with
                  | intro hs hpTok =>
                      cases hqData with
                      | intro ht hqTok =>
                          have hst : hsame s t :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D) (h := h)
                              (s := s) (t := t) policy hD hs ht
                          exact
                            ⟨s, t, hD, hs, ht, hpTok, hqTok, hst,
                              psame.intro hpTok hqTok hst⟩

theorem signature_gap_separation_from_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h -> InGapSig bundle D q h ->
      exists s : BHist, exists t : BHist,
        InDom D h /\ SigRel bundle h s /\ SigRel bundle h t /\
          TokIntro bundle s p /\ TokIntro bundle t q /\ hsame s t /\ psame bundle p q := by
  intro policy hp hq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro hD hpWitness =>
      cases hq with
      | intro _ hqWitness =>
          cases hpWitness with
          | intro s hpData =>
              cases hqWitness with
              | intro t hqData =>
                  cases hpData with
                  | intro hs hpTok =>
                      cases hqData with
                      | intro ht hqTok =>
                          have hst : hsame s t :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D) (h := h)
                              (s := s) (t := t) policy hD hs ht
                          exact
                            ⟨s, t, hD, hs, ht, hpTok, hqTok, hst,
                              psame.intro hpTok hqTok hst⟩

theorem policy_gap_separation_signature_hsame [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → InGapSig bundle D p h → InGapSig bundle D q h →
      ∃ s : BHist, ∃ t : BHist, SigRel bundle h s ∧ SigRel bundle h t ∧ hsame s t := by
  intro policy hp hq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro hD hpWitness =>
      cases hq with
      | intro _ hqWitness =>
          cases hpWitness with
          | intro s hpData =>
              cases hqWitness with
              | intro t hqData =>
                  cases hpData with
                  | intro hs _ =>
                      cases hqData with
                      | intro ht _ =>
                          have hst : hsame s t :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D) (h := h)
                              (s := s) (t := t) policy hD hs ht
                          exact ⟨s, t, hs, ht, hst⟩

theorem internalized_gap_separation_packed [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h /\ InGapSig bundle D q h ->
      psame bundle p q := by
  intro policy memberships
  cases memberships with
  | intro hp hq =>
      have witness :=
        policy_gap_separation_with_domain_witnesses
          (bundle := bundle) (D := D) (h := h) (p := p) (q := q) policy hp hq
      cases witness with
      | intro s rest =>
          cases rest with
          | intro t data =>
              exact data.right.right.right.right.right.right

theorem gap_separation_same_signature_witness_pair [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h -> InGapSig bundle D q h ->
      (exists s : BHist, exists t : BHist, SigRel bundle h s /\ SigRel bundle h t /\
        hsame s t) /\ psame bundle p q := by
  intro policy hp hq
  constructor
  · exact
      policy_gap_separation_signature_hsame
        (bundle := bundle) (D := D) (h := h) (p := p) (q := q) policy hp hq
  · exact
      internalized_gap_separation_packed
        (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
        policy (And.intro hp hq)

theorem proof_sprint_gap_separation [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h -> InGapSig bundle D q h ->
      psame bundle p q := by
  intro policy hp hq
  exact
    internalized_gap_separation_packed
      (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
      policy (And.intro hp hq)

theorem gap_separation_concrete [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h -> InGapSig bundle D q h ->
      psame bundle p q := by
  intro policy hp hq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro hD hpWitness =>
      cases hq with
      | intro _ hqWitness =>
          cases hpWitness with
          | intro s hpData =>
              cases hqWitness with
              | intro t hqData =>
                  cases hpData with
                  | intro hs hpTok =>
                      cases hqData with
                      | intro ht hqTok =>
                          have hst : hsame s t :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D) (h := h)
                              (s := s) (t := t) policy hD hs ht
                          exact psame.intro hpTok hqTok hst

theorem policy_gap_separation_pair [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → InGapSig bundle D p h ∧ InGapSig bundle D q h →
      psame bundle p q ∧
        ∃ s : BHist, ∃ t : BHist, SigRel bundle h s ∧ SigRel bundle h t ∧ hsame s t := by
  intro policy memberships
  cases memberships with
  | intro hp hq =>
      have samePkg : psame bundle p q :=
        internalized_gap_separation_packed
          (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
          policy (And.intro hp hq)
      have sameSig :
          ∃ s : BHist, ∃ t : BHist, SigRel bundle h s ∧ SigRel bundle h t ∧ hsame s t :=
        policy_gap_separation_signature_hsame
          (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
          policy hp hq
      exact And.intro samePkg sameSig

theorem gap_separation_with_domain_pair [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h -> InGapSig bundle D q h ->
      InDom D h ∧ psame bundle p q := by
  intro policy hp hq
  have witness :=
    policy_gap_separation_with_domain_witnesses
      (bundle := bundle) (D := D) (h := h) (p := p) (q := q) policy hp hq
  cases witness with
  | intro s rest =>
      cases rest with
      | intro t data =>
          exact And.intro data.left data.right.right.right.right.right.right

end BEDC.FKernel.Gap
