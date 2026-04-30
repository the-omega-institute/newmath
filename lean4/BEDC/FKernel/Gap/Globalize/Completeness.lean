import BEDC.FKernel.Gap.Globalize

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

theorem concrete_globalization_completeness_samesig [AskSetup] [PackageSetup] [DomainSetup]
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

theorem concrete_globalize_classifies_token_witness_directions [AskSetup] [PackageSetup]
    [DomainSetup] {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist}
    {p q : Pkg} (askPolicy : AskPolicy (InDom D))
    (packagePolicy : PackageTokenPolicy bundle) (hp : InGapSig bundle D p h)
    (hq : InGapSig bundle D q k) :
    (psame bundle p q → ∃ s : BHist, ∃ t : BHist,
      SigRel bundle h s ∧ SigRel bundle k t ∧
        TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t) ∧
      ((∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ SigRel bundle k t ∧
          TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t) →
        psame bundle p q) := by
  have _askPolicy : AskPolicy (InDom D) := askPolicy
  constructor
  · intro samePkg
    exact internalized_globalize_completeness_with_tokens
      (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
      packagePolicy hp hq samePkg
  · intro witnesses
    cases witnesses with
    | intro s rest =>
        cases rest with
        | intro t data =>
            cases data with
            | intro _ tail =>
                cases tail with
                | intro _ tokenData =>
                    cases tokenData with
                    | intro leftTok tokenTail =>
                        cases tokenTail with
                        | intro rightTok sameHist =>
                            exact packagePolicy.soundness leftTok rightTok sameHist

end BEDC.FKernel.Gap
