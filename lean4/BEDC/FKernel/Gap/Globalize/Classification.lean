import BEDC.FKernel.Gap.Globalize
import BEDC.FKernel.Gap.Globalize.Completeness

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

theorem proof_sprint_globalization_classifies_by_signatures [AskSetup] [PackageSetup]
    [DomainSetup] {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    psame bundle p q ↔ ∃ s : BHist, ∃ t : BHist,
      SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t := by
  exact internalized_globalize_classifies_by_signatures
    (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
    askPolicy packagePolicy hp hq

theorem concrete_globalize_classifies_symmetric_package_pair [AskSetup] [PackageSetup]
    [DomainSetup] {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (hp : InGapSig bundle D p h) (hq : InGapSig bundle D q k) :
    (psame bundle p q ↔ ∃ s : BHist, ∃ t : BHist,
      SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t) ∧
    (psame bundle q p ↔ ∃ t : BHist, ∃ s : BHist,
      SigRel bundle k t ∧ SigRel bundle h s ∧ hsame t s) := by
  exact And.intro
    (concrete_globalize_classifies_by_signatures_primary
      (bundle := bundle) (D := D) (h := h) (k := k) (p := p) (q := q)
      askPolicy packagePolicy hp hq)
    (concrete_globalize_classifies_by_signatures_primary
      (bundle := bundle) (D := D) (h := k) (k := h) (p := q) (q := p)
      askPolicy packagePolicy hq hp)

theorem active_reading_policy_dependency_fields [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain}
    (askPolicy : AskPolicy (InDom D)) (packagePolicy : PackageTokenPolicy bundle)
    (tokenExists : ∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) :
    (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      (∀ {h k : BHist} {p q : Pkg},
        InGapSig bundle D p h → InGapSig bundle D q k → psame bundle p q →
          ∃ s : BHist, ∃ t : BHist,
            SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t) ∧
      (∀ {h k : BHist} {p q : Pkg},
        InGapSig bundle D p h → InGapSig bundle D q k →
          (∃ s : BHist, ∃ t : BHist,
            SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t) → psame bundle p q) := by
  exact active_reading_policy_dependencies
    (bundle := bundle) (D := D) askPolicy packagePolicy tokenExists

end BEDC.FKernel.Gap
