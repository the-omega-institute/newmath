import BEDC.FKernel.Gap.Construction

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

variable [AskSetup] [PackageSetup] [G : DomainSetup]
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

theorem globalize_completeness_primary [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → InGapSig bundle D p h → InGapSig bundle D q k →
      psame bundle p q →
      ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t := by
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

theorem concrete_globalize_completeness_sameSig [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → InGapSig bundle D p h → InGapSig bundle D q k →
      psame bundle p q → SameSig bundle h k := by
  intro packagePolicy hp hq hpq
  exact concrete_globalize_completeness
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    packagePolicy hp hq hpq

theorem globalize_completeness_from_package_reflection [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> InGapSig bundle D p h -> InGapSig bundle D q k ->
      psame bundle p q -> SameSig bundle h k := by
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

theorem globalize_completeness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → InGapSig bundle D p h → InGapSig bundle D q k →
      psame bundle p q → SameSig bundle h k := by
  exact globalize_completeness_from_package_reflection

theorem concrete_globalize_completeness_from_package_same
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (packagePolicy : PackageTokenPolicy bundle) :
    InGapSig bundle D p h -> InGapSig bundle D q k -> psame bundle p q ->
      SameSig bundle h k := by
  intro hp hq hpq
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

theorem internalized_globalize_completeness_projection [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> InGapSig bundle D p h -> InGapSig bundle D q k ->
      psame bundle p q ->
      exists s : BHist, exists t : BHist,
        SigRel bundle h s /\ SigRel bundle k t /\ hsame s t := by
  intro packagePolicy hp hq hpq
  exact internalized_globalize_completeness packagePolicy hp hq hpq

theorem concrete_globalize_soundness_intro
    {bundle : ProbeBundle ProbeName} {h k s t : BHist} {p q : Pkg} :
    SigRel bundle h s → SigRel bundle k t → TokIntro bundle s p →
      TokIntro bundle t q → hsame s t → psame bundle p q := by
  have _domainSetup := G
  intro _ _ hp hq hst
  exact psame.intro hp hq hst

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

theorem concrete_globalize_soundness_from_sameSig
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle) :
    InGapSig bundle D p h -> InGapSig bundle D q k -> SameSig bundle h k ->
      psame bundle p q := by
  intro hp hq sameSig
  exact internalized_globalize_soundness askPolicy packagePolicy hp hq sameSig

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

theorem internalized_globalize_classifies_iff [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    psame bundle p q <-> exists s : BHist, exists t : BHist,
      SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t := by
  exact internalized_globalize_classifies_by_signatures
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    askPolicy packagePolicy hp hq

omit [AskSetup] [PackageSetup] G in
theorem concrete_globalize_classifies_sameSig [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    psame bundle p q ↔ SameSig bundle h k := by
  exact concrete_globalize_classifies_by_signatures
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    askPolicy packagePolicy hp hq

theorem concrete_globalize_classifies_sameSig_mp
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    psame bundle p q → SameSig bundle h k := by
  intro hpq
  exact (concrete_globalize_classifies_sameSig
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    askPolicy packagePolicy hp hq).mp hpq

theorem concrete_globalize_classifies_by_signatures_directions [AskSetup] [PackageSetup]
    [DomainSetup] {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    (psame bundle p q →
        ∃ s : BHist, ∃ t : BHist,
          SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t) ∧
      ((∃ s : BHist, ∃ t : BHist,
          SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t) →
        psame bundle p q) := by
  have classified :
      psame bundle p q ↔
        ∃ s : BHist, ∃ t : BHist,
          SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t :=
    concrete_globalize_classifies_by_signatures
      (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
      askPolicy packagePolicy hp hq
  constructor
  · exact classified.mp
  · exact classified.mpr

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

theorem active_reading_policy_dependencies
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D))
    (packagePolicy : PackageTokenPolicy bundle)
    (tokenExists : forall s : BHist, exists p : Pkg, TokIntro bundle s p) :
    (forall {h : BHist}, InDom D h -> exists p : Pkg, InGapSig bundle D p h) /\
    (forall {h k : BHist} {p q : Pkg},
      InGapSig bundle D p h -> InGapSig bundle D q k -> psame bundle p q ->
        exists s : BHist, exists t : BHist,
          SigRel bundle h s /\ SigRel bundle k t /\ hsame s t) /\
    (forall {h k : BHist} {p q : Pkg},
      InGapSig bundle D p h -> InGapSig bundle D q k ->
        (exists s : BHist, exists t : BHist,
          SigRel bundle h s /\ SigRel bundle k t /\ hsame s t) -> psame bundle p q) := by
  have classification :=
    exact_globalize_classifies_signatures
      (bundle := bundle) (D := D) askPolicy packagePolicy tokenExists
  constructor
  · exact classification.left
  · constructor
    · intro h k p q hp hq samePkg
      exact (classification.right hp hq).mp samePkg
    · intro h k p q hp hq sameSig
      exact (classification.right hp hq).mpr sameSig
end BEDC.FKernel.Gap
