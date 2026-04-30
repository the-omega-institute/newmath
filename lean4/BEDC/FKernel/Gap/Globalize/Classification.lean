import BEDC.FKernel.Gap.Globalize

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

end BEDC.FKernel.Gap
