import BEDC.FKernel.Gap.Policy

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

variable [AskSetup] [PackageSetup] [G : DomainSetup]
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

theorem inGapSig_same_source_full_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h -> InGapSig bundle D q h ->
      exists s : BHist, exists t : BHist,
        InDom D h /\ SigRel bundle h s /\ SigRel bundle h t /\
          TokIntro bundle s p /\ TokIntro bundle t q /\ hsame s t := by
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
                              (And.intro hIn
                                (And.intro hs
                                  (And.intro ht
                                    (And.intro hpTok
                                      (And.intro hqTok hst))))))

theorem inGapSig_same_source_package_witnesses [AskSetup] [PackageSetup] [DomainSetup]
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

omit [AskSetup] [PackageSetup] G in
theorem gap_memberships_share_signature [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) -> InGapSig bundle D p h -> InGapSig bundle D q h ->
      exists s : BHist, exists t : BHist,
        SigRel bundle h s /\ SigRel bundle h t /\ hsame s t := by
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
                            (Exists.intro t
                              (And.intro hs
                                (And.intro ht hst)))

theorem concrete_gap_separation
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) :
    InGapSig bundle D p h -> InGapSig bundle D q h -> psame bundle p q := by
  intro hp hq
  exact internalized_gap_separation
    (bundle := bundle) (D := D) (h := h) (p := p) (q := q)
    askPolicy hp hq

theorem concrete_gap_separation_witnesses
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) :
    InGapSig bundle D p h → InGapSig bundle D q h →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ TokIntro bundle s p ∧
          SigRel bundle h t ∧ TokIntro bundle t q ∧
            hsame s t ∧ psame bundle p q := by
  intro hp hq
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
                                (And.intro hpTok
                                  (And.intro ht
                                    (And.intro hqTok
                                      (And.intro hst hpq))))))


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

theorem concrete_gap_coverage
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist}
    (askPolicy : AskPolicy (InDom D))
    (tokenExists : forall s : BHist, exists p : Pkg, TokIntro bundle s p) :
    InDom D h -> exists p : Pkg, InGapSig bundle D p h := by
  intro hIn
  have hSigTotal := policy_sig_total (bundle := bundle) (D := D) (h := h) askPolicy hIn
  cases hSigTotal with
  | intro s hs =>
      cases tokenExists s with
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

theorem policy_gap_separation_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    AskPolicy (InDom D) → PackageTokenPolicy bundle →
      InGapSig bundle D p h → InGapSig bundle D q h →
        ∃ s : BHist, ∃ t : BHist,
          SigRel bundle h s ∧ SigRel bundle h t ∧
            TokIntro bundle s p ∧ TokIntro bundle t q ∧
              hsame s t ∧ psame bundle p q := by
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
                          have hpq : psame bundle p q :=
                            packagePolicy.soundness hpTok hqTok hst
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro hs
                                (And.intro ht
                                  (And.intro hpTok
                                    (And.intro hqTok
                                      (And.intro hst hpq))))))

theorem gap_separation_policy [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    DomainPolicy D → AskPolicy (InDom D) → PackageTokenPolicy bundle →
      InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q := by
  intro _ askPolicy packagePolicy hp hq
  cases inGapSig_witness_pair (bundle := bundle) (D := D) (p := p) (h := h) hp with
  | intro s hpData =>
      cases inGapSig_witness_pair (bundle := bundle) (D := D) (p := q) (h := h) hq with
      | intro t hqData =>
          cases hpData with
          | intro hIn hpRest =>
              cases hpRest with
              | intro hs hpTok =>
                  cases hqData with
                  | intro _ hqRest =>
                      cases hqRest with
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

omit [AskSetup] [PackageSetup] G in
theorem internalized_concrete_globalize_instance [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D))
    (packagePolicy : PackageTokenPolicy bundle)
    (tokenExists : ∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) :
    GapPolicy bundle D := by
  exact concrete_gap_policy
    (bundle := bundle) (D := D)
    askPolicy packagePolicy tokenExists

theorem first_concrete_globalization_ledger [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D))
    (packagePolicy : PackageTokenPolicy bundle)
    (tokenExists : ∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) :
    GapPolicy bundle D := by
  exact concrete_gap_policy
    (bundle := bundle) (D := D)
    askPolicy packagePolicy tokenExists
end BEDC.FKernel.Gap
