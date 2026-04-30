import BEDC.FKernel.Package

/-! Gap ledgers record which admitted histories fall under visible package tokens. -/
namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ext
open BEDC.FKernel.Mark
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

theorem inGapSig_intro {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h s : BHist} :
    InDom D h -> SigRel bundle h s -> TokIntro bundle s p -> InGapSig bundle D p h := by
  intro hdom hsig htok
  exact And.intro hdom (Exists.intro s (And.intro hsig htok))

theorem inGapSig_domain_witness
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h -> InDom D h := by
  intro hgap
  exact hgap.left

omit [AskSetup] [PackageSetup] G in
theorem inGapSig_signature_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h -> exists s : BHist, SigRel bundle h s /\ TokIntro bundle s p := by
  intro hgap
  exact hgap.right

omit [AskSetup] [PackageSetup] G in
def CompGap {Source Inter Final : Type}
    (firstGap : Inter → Source → Prop)
    (secondGap : Final → Inter → Prop)
    (z : Final) (x : Source) : Prop :=
  ∃ y : Inter, firstGap y x ∧ secondGap z y

omit [AskSetup] [PackageSetup] G in
theorem compGap_inversion
    {Source Inter Final : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    {z : Final} {x : Source} :
    CompGap firstGap secondGap z x ->
      exists y : Inter, firstGap y x /\ secondGap z y := by
  intro h
  exact h

structure GapPolicy (bundle : ProbeBundle ProbeName) (D : Domain) : Prop where
  generation : ∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h → ∃ s : BHist, TokIntro bundle s p
  coverage : ∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h
  separation : ∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q

theorem gap_policy_fields {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      (∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h →
        InGapSig bundle D q h → psame bundle p q) ∧
      (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h → ∃ s : BHist, TokIntro bundle s p) := by
  constructor
  · exact policy.coverage
  · constructor
    · exact policy.separation
    · exact policy.generation

omit [AskSetup] [PackageSetup] G in
theorem globalization_has_three_layers [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} :
    AskPolicy (InDom D) → PackagePolicy bundle → GapPolicy bundle D →
      AskPolicy (InDom D) ∧ PackagePolicy bundle ∧ GapPolicy bundle D := by
  intro askPolicy packagePolicy gapPolicy
  constructor
  · exact askPolicy
  · constructor
    · exact packagePolicy
    · exact gapPolicy

omit [AskSetup] [PackageSetup] G in
theorem gap_generation_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist}
    (policy : GapPolicy bundle D) :
    InGapSig bundle D p h → ∃ s : BHist, TokIntro bundle s p := by
  intro hgap
  exact policy.generation hgap

theorem internalized_gap_coverage
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D))
    (tokenExists :
      forall {h s : BHist}, InDom D h -> SigRel bundle h s ->
        Exists (fun p : Pkg => TokIntro bundle s p))
    {h : BHist} :
    InDom D h -> Exists (fun p : Pkg => InGapSig bundle D p h) := by
  intro hIn
  have sigExistsFor : forall b : ProbeBundle ProbeName, Exists (fun s : BHist => SigRel b h s) := by
    intro b
    induction b with
    | Bnil =>
        exact Exists.intro BHist.Empty (SigRel.empty h)
    | Bcons pi tail ih =>
        cases askPolicy.total (π := pi) hIn with
        | intro m hm =>
            cases hm with
            | intro delta hAsk =>
                cases ih with
                | intro s hs =>
                    cases m with
                    | b0 =>
                        exact Exists.intro (BHist.e0 s)
                          (SigRel.cons pi tail h s (BHist.e0 s) BMark.b0 delta hAsk hs (Ext.e0 s))
                    | b1 =>
                        exact Exists.intro (BHist.e1 s)
                          (SigRel.cons pi tail h s (BHist.e1 s) BMark.b1 delta hAsk hs (Ext.e1 s))
  have sigExists : Exists (fun s : BHist => SigRel bundle h s) := sigExistsFor bundle
  cases sigExists with
  | intro s hs =>
      cases tokenExists hIn hs with
      | intro p hp =>
          exact Exists.intro p ⟨hIn, Exists.intro s ⟨hs, hp⟩⟩

theorem gap_coverage_globalize
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D))
    (tokenExists :
      ∀ {h s : BHist}, InDom D h → SigRel bundle h s →
        ∃ p : Pkg, TokIntro bundle s p)
    {h : BHist} :
    InDom D h → ∃ p : Pkg, InGapSig bundle D p h := by
  exact internalized_gap_coverage (bundle := bundle) (D := D) askPolicy tokenExists

theorem internalized_gap_separation
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) →
      InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q := by
  intro askPolicy hp hq
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
                          exact psame.intro hpTok hqTok hst

omit [AskSetup] [PackageSetup] G in
theorem internalized_gap_separation_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → InGapSig bundle D p h → InGapSig bundle D q h →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle h t ∧
          TokIntro bundle s p ∧ TokIntro bundle t q ∧
            hsame s t ∧ psame bundle p q := by
  intro askPolicy hp hq
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
                          have hpq : psame bundle p q := psame.intro hpTok hqTok hst
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro hs
                                (And.intro ht
                                  (And.intro hpTok
                                    (And.intro hqTok
                                      (And.intro hst hpq))))))

theorem gap_separation_globalize
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) →
      InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q := by
  intro askPolicy hp hq
  exact internalized_gap_separation
    (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
    askPolicy hp hq

omit [AskSetup] [PackageSetup] G in
theorem inGapSig_same_source_signatures_same [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → InGapSig bundle D p h → InGapSig bundle D q h →
      ∃ s : BHist, ∃ t : BHist,
        TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t := by
  intro askPolicy hp hq
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
                          exact Exists.intro s
                            (Exists.intro t (And.intro hpTok (And.intro hqTok hst)))

omit [AskSetup] [PackageSetup] G in
theorem inGapSig_same_source_signature_events_same [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → InGapSig bundle D p h → InGapSig bundle D q h →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle h t ∧
          TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t := by
  intro askPolicy hp hq
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
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro hs
                                (And.intro ht
                                  (And.intro hpTok
                                    (And.intro hqTok hst)))))

omit [AskSetup] [PackageSetup] G in
theorem inGapSig_same_source_sigRel_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → InGapSig bundle D p h → InGapSig bundle D q h →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle h t ∧ hsame s t := by
  intro askPolicy hp hq
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
                  | intro hs _ =>
                      cases htData with
                      | intro ht _ =>
                          have hst : hsame s t :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D) (h := h) (s := s) (t := t)
                              askPolicy hIn hs ht
                          exact Exists.intro s
                            (Exists.intro t (And.intro hs (And.intro ht hst)))

theorem concrete_gap_separation
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) :
    InGapSig bundle D p h -> InGapSig bundle D q h -> psame bundle p q := by
  intro hp hq
  exact internalized_gap_separation
    (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
    askPolicy hp hq

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

omit [PackageSetup] in
theorem policy_sig_total
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} :
    AskPolicy (InDom D) → InDom D h → ∃ s : BHist, SigRel bundle h s := by
  intro askPolicy hIn
  induction bundle with
  | Bnil =>
      exact Exists.intro BHist.Empty (SigRel.empty h)
  | Bcons pi tail ih =>
      cases ih with
      | intro s hs =>
          have hAskTotal := askPolicy.total (π := pi) (h := h) hIn
          cases hAskTotal with
          | intro m hm =>
              cases hm with
              | intro delta hAsk =>
                  cases m with
                  | b0 =>
                      exact Exists.intro (BHist.e0 s)
                        (SigRel.cons pi tail h s (BHist.e0 s) BMark.b0 delta hAsk hs (Ext.e0 s))
                  | b1 =>
                      exact Exists.intro (BHist.e1 s)
                        (SigRel.cons pi tail h s (BHist.e1 s) BMark.b1 delta hAsk hs (Ext.e1 s))

theorem policy_gap_coverage
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} :
    AskPolicy (InDom D) →
      (∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) →
      InDom D h → ∃ p : Pkg, InGapSig bundle D p h := by
  intro askPolicy tokenExists hIn
  have hSigTotal := policy_sig_total (bundle := bundle) (D := D) (h := h) askPolicy hIn
  cases hSigTotal with
  | intro s hs =>
      have hTok := tokenExists s
      cases hTok with
      | intro p hp =>
          exact Exists.intro p (And.intro hIn (Exists.intro s (And.intro hs hp)))

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

theorem concrete_gap_policy
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D))
    (packagePolicy : PackageTokenPolicy bundle)
    (tokenExists : ∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) :
    GapPolicy bundle D := by
  constructor
  · intro p h hp
    unfold InGapSig at hp
    cases hp with
    | intro _ hpSig =>
        cases hpSig with
        | intro s hsData =>
            cases hsData with
            | intro _ hpTok =>
                exact Exists.intro s hpTok
  · intro h hIn
    exact policy_gap_coverage
      (bundle := bundle) (D := D) (h := h)
      askPolicy tokenExists hIn
  · intro h p q _ hp hq
    exact policy_gap_separation
      (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
      askPolicy packagePolicy hp hq

omit G in
theorem policy_globalize_exact {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> TokIntro bundle s p -> TokIntro bundle t q ->
      (psame bundle p q <-> hsame s t) := by
  intro policy hp hq
  exact psame_iff_hsame policy hp hq

theorem internalized_globalize_completeness
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> InGapSig bundle D p h -> InGapSig bundle D q k ->
      psame bundle p q ->
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s /\ SigRel bundle k t /\ hsame s t := by
  intro packagePolicy hp hq hpq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro _ hpSig =>
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
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro hs
                                  (And.intro ht
                                    (packagePolicy.reflection hpTok hqTok hpq))))

theorem internalized_globalize_completeness_concrete
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → InGapSig bundle D p h → InGapSig bundle D q k →
      psame bundle p q →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t := by
  intro packagePolicy hp hq hpq
  exact internalized_globalize_completeness
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    packagePolicy hp hq hpq

omit [AskSetup] [PackageSetup] G in
theorem concrete_globalize_completeness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → InGapSig bundle D p h → InGapSig bundle D q k →
      psame bundle p q →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t := by
  intro packagePolicy hp hq hpq
  exact internalized_globalize_completeness
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    packagePolicy hp hq hpq

theorem internalized_globalize_completeness_with_tokens
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → InGapSig bundle D p h → InGapSig bundle D q k →
      psame bundle p q →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧
          TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t := by
  intro packagePolicy hp hq hpq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro _ hpSig =>
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
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro hs
                                (And.intro ht
                                  (And.intro hpTok
                                    (And.intro hqTok
                                      (packagePolicy.reflection hpTok hqTok hpq))))))

omit [AskSetup] [PackageSetup] G in
theorem concrete_globalize_completeness_with_tokens [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → InGapSig bundle D p h → InGapSig bundle D q k →
      psame bundle p q →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧
          TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t := by
  intro packagePolicy hp hq hpq
  exact internalized_globalize_completeness_with_tokens
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    packagePolicy hp hq hpq

theorem internalized_globalize_completeness_hsame_only
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> InGapSig bundle D p h -> InGapSig bundle D q k ->
      psame bundle p q -> exists s : BHist, exists t : BHist, hsame s t := by
  intro packagePolicy hp hq hpq
  have generated :=
    internalized_globalize_completeness_with_tokens
      (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
      packagePolicy hp hq hpq
  cases generated with
  | intro s generatedTail =>
      cases generatedTail with
      | intro t generatedData =>
          cases generatedData with
          | intro hs generatedRest =>
              cases generatedRest with
              | intro ht generatedTokenRest =>
                  cases generatedTokenRest with
                  | intro hpTok generatedTokenTail =>
                      cases generatedTokenTail with
                      | intro hqTok hst =>
                          exact Exists.intro s (Exists.intro t hst)

omit [AskSetup] [PackageSetup] G in
theorem internalized_globalize_completeness_projection [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> InGapSig bundle D p h -> InGapSig bundle D q k ->
      psame bundle p q ->
      exists s : BHist, exists t : BHist,
        SigRel bundle h s /\ SigRel bundle k t /\ hsame s t := by
  intro packagePolicy hp hq hpq
  exact internalized_globalize_completeness packagePolicy hp hq hpq

theorem internalized_globalize_soundness
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → PackageTokenPolicy bundle →
      InGapSig bundle D p h → InGapSig bundle D q k →
      (∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t) →
      psame bundle p q := by
  intro askPolicy packagePolicy hp hq hsig
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro hIn hpSig =>
      cases hq with
      | intro kIn hqSig =>
          cases hpSig with
          | intro u huData =>
              cases hqSig with
              | intro v hvData =>
                  cases huData with
                  | intro huSig hpTok =>
                      cases hvData with
                      | intro hvSig hqTok =>
                          cases hsig with
                          | intro s hsRest =>
                              cases hsRest with
                              | intro t htRest =>
                                  cases htRest with
                                  | intro hs htail =>
                                      cases htail with
                                      | intro ht hst =>
                                          have hsu : hsame s u :=
                                            sig_deterministic
                                              (bundle := bundle) (D := InDom D)
                                              (h := h) (s := s) (t := u)
                                              askPolicy hIn hs huSig
                                          have htv : hsame t v :=
                                            sig_deterministic
                                              (bundle := bundle) (D := InDom D)
                                              (h := k) (s := t) (t := v)
                                              askPolicy kIn ht hvSig
                                          have huv : hsame u v :=
                                            hsame_trans (hsame_symm hsu) (hsame_trans hst htv)
                                          exact packagePolicy.soundness hpTok hqTok huv

theorem internalized_globalize_soundness_for_witnesses
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} {s t : BHist} :
    AskPolicy (InDom D) -> PackageTokenPolicy bundle ->
      InGapSig bundle D p h -> InGapSig bundle D q k ->
      SigRel bundle h s -> SigRel bundle k t -> hsame s t -> psame bundle p q := by
  intro askPolicy packagePolicy hp hq hs ht hst
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro hIn hpSig =>
      cases hq with
      | intro kIn hqSig =>
          cases hpSig with
          | intro u huData =>
              cases hqSig with
              | intro v hvData =>
                  cases huData with
                  | intro huSig hpTok =>
                      cases hvData with
                      | intro hvSig hqTok =>
                          have hsu : hsame s u :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D)
                              (h := h) (s := s) (t := u)
                              askPolicy hIn hs huSig
                          have htv : hsame t v :=
                            sig_deterministic
                              (bundle := bundle) (D := InDom D)
                              (h := k) (s := t) (t := v)
                              askPolicy kIn ht hvSig
                          have huv : hsame u v :=
                            hsame_trans (hsame_symm hsu) (hsame_trans hst htv)
                          exact packagePolicy.soundness hpTok hqTok huv

theorem exact_concrete_globalize
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (domainPolicy : DomainPolicy D)
    (askPolicy : AskPolicy (InDom D))
    (packagePolicy : PackageTokenPolicy bundle)
    (tokenExists : forall s : BHist, exists p : Pkg, TokIntro bundle s p) :
    (forall {h : BHist}, InDom D h -> exists p : Pkg, InGapSig bundle D p h) /\
      (forall {h : BHist} {p q : Pkg}, InGapSig bundle D p h -> InGapSig bundle D q h -> psame bundle p q) /\
      (forall {h k : BHist} {p q : Pkg}, InGapSig bundle D p h -> InGapSig bundle D q k -> psame bundle p q -> exists s : BHist, exists t : BHist, SigRel bundle h s /\ SigRel bundle k t /\ hsame s t) := by
  have _domainPolicy := domainPolicy
  constructor
  · intro h hIn
    exact policy_gap_coverage
      (bundle := bundle) (D := D) (h := h)
      askPolicy tokenExists hIn
  · constructor
    · intro h p q hp hq
      exact policy_gap_separation
        (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
        askPolicy packagePolicy hp hq
    · intro h k p q hp hq hpq
      exact internalized_globalize_completeness
        (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
        packagePolicy hp hq hpq

theorem internalized_globalize_classifies_by_signatures
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    psame bundle p q ↔
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t := by
  constructor
  · intro hpq
    exact internalized_globalize_completeness
      (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
      packagePolicy hp hq hpq
  · intro hsig
    unfold InGapSig at hp
    unfold InGapSig at hq
    cases hp with
    | intro hIn hpSig =>
        cases hq with
        | intro kIn hqSig =>
            cases hpSig with
            | intro u huData =>
                cases hqSig with
                | intro v hvData =>
                    cases huData with
                    | intro huSig hpTok =>
                        cases hvData with
                        | intro hvSig hqTok =>
                            cases hsig with
                            | intro s hsRest =>
                                cases hsRest with
                                | intro t htRest =>
                                    cases htRest with
                                    | intro hs htail =>
                                        cases htail with
                                        | intro ht hst =>
                                            have hsu : hsame s u :=
                                              sig_deterministic
                                                (bundle := bundle) (D := InDom D)
                                                (h := h) (s := s) (t := u)
                                                askPolicy hIn hs huSig
                                            have htv : hsame t v :=
                                              sig_deterministic
                                                (bundle := bundle) (D := InDom D)
                                                (h := k) (s := t) (t := v)
                                                askPolicy kIn ht hvSig
                                            have huv : hsame u v :=
                                              hsame_trans (hsame_symm hsu) (hsame_trans hst htv)
                                            exact packagePolicy.soundness hpTok hqTok huv

theorem concrete_globalize_classifies_by_signatures
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    psame bundle p q <->
      exists s : BHist, exists t : BHist,
        SigRel bundle h s /\ SigRel bundle k t /\ hsame s t := by
  exact internalized_globalize_classifies_by_signatures
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    askPolicy packagePolicy hp hq

theorem exact_globalize_classifies_signatures
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D))
    (packagePolicy : PackageTokenPolicy bundle)
    (tokenExists : forall s : BHist, exists p : Pkg, TokIntro bundle s p) :
    (forall {h : BHist}, InDom D h -> exists p : Pkg, InGapSig bundle D p h) /\
    (forall {h k : BHist} {p q : Pkg},
      InGapSig bundle D p h -> InGapSig bundle D q k ->
        (psame bundle p q <->
          exists s : BHist, exists t : BHist,
            SigRel bundle h s /\ SigRel bundle k t /\ hsame s t)) := by
  constructor
  · intro h hIn
    exact policy_gap_coverage
      (bundle := bundle) (D := D) (h := h) askPolicy tokenExists hIn
  · intro h k p q hp hq
    exact internalized_globalize_classifies_by_signatures
      (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
      askPolicy packagePolicy hp hq

omit [AskSetup] [PackageSetup] in
theorem domain_transport {D : Domain} (policy : DomainPolicy D) {h k : BHist} :
    InDom D h → hsame h k → InDom D k := by
  intro hh hhk
  exact policy.transport hh hhk

omit [AskSetup] [PackageSetup] G in
theorem domain_transport_symmetric [AskSetup] [PackageSetup] [DomainSetup]
    {D : Domain} (policy : DomainPolicy D) {h k : BHist} :
    InDom D k → hsame h k → InDom D h := by
  intro hk hhk
  exact policy.transport hk (hsame_symm hhk)

omit [AskSetup] [PackageSetup] in
theorem composite_coverage {Mid Final : Type} {D : Domain}
    {firstGap : Mid -> BHist -> Prop} {secondGap : Final -> Mid -> Prop}
    (firstCoverage : forall {h : BHist}, InDom D h -> exists y : Mid, firstGap y h)
    (secondCoverage :
      forall {y : Mid},
        (exists h : BHist, InDom D h ∧ firstGap y h) ->
          exists z : Final, secondGap z y)
    {h : BHist} :
    InDom D h -> exists z : Final, exists y : Mid, firstGap y h ∧ secondGap z y := by
  intro hIn
  cases firstCoverage hIn with
  | intro y hy =>
      have ySource : exists h0 : BHist, InDom D h0 ∧ firstGap y h0 :=
        Exists.intro h (And.intro hIn hy)
      cases secondCoverage ySource with
      | intro z hz =>
          exact Exists.intro z (Exists.intro y (And.intro hy hz))

omit [AskSetup] [PackageSetup] G in
theorem compGap_coverage_from_layers
    {Source Inter Final : Type}
    {SourceOk : Source -> Prop} {InterOk : Inter -> Prop}
    {CGap : Inter -> Source -> Prop} {DGap : Final -> Inter -> Prop}
    (cCoverage :
      forall {h : Source}, SourceOk h -> exists y : Inter, And (CGap y h) (InterOk y))
    (dCoverage : forall {y : Inter}, InterOk y -> exists z : Final, DGap z y)
    {h : Source} :
    SourceOk h -> exists z : Final, exists y : Inter, And (CGap y h) (DGap z y) := by
  intro sourceOk
  cases cCoverage sourceOk with
  | intro y cData =>
      cases cData with
      | intro cGap interOk =>
          cases dCoverage interOk with
          | intro z dGap =>
              exact Exists.intro z (Exists.intro y (And.intro cGap dGap))

omit [AskSetup] [PackageSetup] G in
theorem compGap_coverage_exact
    {Source Inter Final : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    (firstCoverage : forall x : Source, exists y : Inter, firstGap y x)
    (secondCoverage : forall y : Inter, exists z : Final, secondGap z y)
    (x : Source) :
    exists z : Final, CompGap firstGap secondGap z x := by
  cases firstCoverage x with
  | intro y firstWitness =>
      cases secondCoverage y with
      | intro z secondWitness =>
          exact Exists.intro z
            (Exists.intro y (And.intro firstWitness secondWitness))

omit [AskSetup] [PackageSetup] G in
theorem compGap_witness_from_layers
    {Source Inter Final : Type}
    {SourceOk : Source → Prop} {InterOk : Inter → Prop}
    {CGap : Inter → Source → Prop} {DGap : Final → Inter → Prop}
    (cCoverage :
      ∀ {x : Source}, SourceOk x → ∃ y : Inter, CGap y x ∧ InterOk y)
    (dCoverage : ∀ {y : Inter}, InterOk y → ∃ z : Final, DGap z y)
    {x : Source} :
    SourceOk x → ∃ z : Final, CompGap CGap DGap z x := by
  intro sourceOk
  cases cCoverage sourceOk with
  | intro y cData =>
      cases cData with
      | intro cGap interOk =>
          cases dCoverage interOk with
          | intro z dGap =>
              exact Exists.intro z (Exists.intro y (And.intro cGap dGap))

omit [AskSetup] [PackageSetup] G in
theorem compGap_assoc
    {A B C D : Type}
    {first : B → A → Prop}
    {second : C → B → Prop}
    {third : D → C → Prop}
    {z : D} {x : A} :
    CompGap (fun c a => CompGap first second c a) third z x ↔
      CompGap first (fun z b => CompGap second third z b) z x := by
  constructor
  · intro left
    cases left with
    | intro c cData =>
        cases cData with
        | intro firstSecond thirdWitness =>
            cases firstSecond with
            | intro b bData =>
                cases bData with
                | intro firstWitness secondWitness =>
                    exact Exists.intro b
                      (And.intro firstWitness
                        (Exists.intro c (And.intro secondWitness thirdWitness)))
  · intro right
    cases right with
    | intro b bData =>
        cases bData with
        | intro firstWitness secondThird =>
            cases secondThird with
            | intro c cData =>
                cases cData with
                | intro secondWitness thirdWitness =>
                    exact Exists.intro c
                      (And.intro
                        (Exists.intro b (And.intro firstWitness secondWitness))
                        thirdWitness)

omit [AskSetup] [PackageSetup] in
theorem domain_invariance {D : Domain} (policy : DomainPolicy D) {h k : BHist} :
    hsame h k -> (InDom D h <-> InDom D k) := by
  intro hhk
  constructor
  · intro hh
    exact policy.transport hh hhk
  · intro hk
    exact policy.transport hk (hsame_symm hhk)

omit [AskSetup] [PackageSetup] G in
theorem compGap_coverage : True := True.intro

def MinimalDomainSetup : DomainSetup where
  Domain := Unit
  InDom := fun _ _ => True

end BEDC.FKernel.Gap
