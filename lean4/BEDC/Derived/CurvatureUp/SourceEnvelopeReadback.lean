import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureChernWeilSourceEnvelope_readback [AskSetup] [PackageSetup]
    {curvatureLedger derham provenance connectionLedger classifier classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
        classifier bundle pkg ->
      Cont provenance connectionLedger classifier' ->
        PkgSig bundle classifier' pkg ->
          hsame classifier classifier' ∧
            CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
              classifier' bundle pkg ∧
              hsame provenance (append curvatureLedger derham) := by
  intro envelope classifierRow' pkgSig'
  have sameClassifier : hsame classifier classifier' :=
    cont_deterministic envelope.right.right.right.right.right.right.left classifierRow'
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed envelope.right.right.left envelope.right.right.right.left classifierRow'
  have classifierReadback' :
      hsame classifier' (append (append curvatureLedger derham) connectionLedger) :=
    hsame_trans classifierRow'
      (congrArg (fun row : BHist => append row connectionLedger)
        envelope.right.right.right.right.right.left)
  have envelope' :
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
        classifier' bundle pkg :=
    And.intro envelope.left
      (And.intro envelope.right.left
        (And.intro envelope.right.right.left
          (And.intro envelope.right.right.right.left
            (And.intro classifierUnary'
              (And.intro envelope.right.right.right.right.right.left
                (And.intro classifierRow'
                  (And.intro classifierReadback' pkgSig')))))))
  exact And.intro sameClassifier
    (And.intro envelope' envelope.right.right.right.right.right.left)

end BEDC.Derived.CurvatureUp
