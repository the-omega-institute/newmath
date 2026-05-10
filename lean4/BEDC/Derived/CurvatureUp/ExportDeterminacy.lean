import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CurvatureChernWeilSourceEnvelope_export_determinacy [AskSetup] [PackageSetup]
    {curvature derham derham' provenance provenance' connectionLedger classifier classifier' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classifier
        bundle pkg ->
      CurvatureChernWeilSourceEnvelope curvature derham' provenance' connectionLedger classifier'
          bundle pkg ->
        hsame derham derham' ->
          hsame provenance provenance' ∧ hsame classifier classifier' := by
  intro envelope envelope' sameDerham
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame (hsame_refl curvature) sameDerham
      envelope.right.right.right.right.right.left
      envelope'.right.right.right.right.right.left
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameProvenance (hsame_refl connectionLedger)
      envelope.right.right.right.right.right.right.left
      envelope'.right.right.right.right.right.right.left
  exact And.intro sameProvenance sameClassifier

end BEDC.Derived.CurvatureUp
