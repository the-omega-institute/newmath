import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureChernWeilSourceEnvelope_provenance_ledger_transport [AskSetup]
    [PackageSetup]
    {curvature derham provenance connectionLedger classifier provenance' classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classifier bundle
        pkg ->
      hsame provenance provenance' ->
        Cont provenance' connectionLedger classifier' ->
          PkgSig bundle classifier' pkg ->
            CurvatureChernWeilSourceEnvelope curvature derham provenance' connectionLedger
                classifier' bundle pkg ∧
              hsame classifier classifier' := by
  intro envelope sameProvenance classifierRow pkgSig'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport envelope.right.right.left sameProvenance
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed provenanceUnary' envelope.right.right.right.left classifierRow
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameProvenance (hsame_refl connectionLedger)
      envelope.right.right.right.right.right.right.left classifierRow
  have provenanceRow' : Cont curvature derham provenance' :=
    cont_result_hsame_transport envelope.right.right.right.right.right.left sameProvenance
  have classifierReadback' : hsame classifier' (append (append curvature derham) connectionLedger) :=
    hsame_trans classifierRow
      (congrArg (fun row : BHist => append row connectionLedger) provenanceRow')
  exact And.intro
    (And.intro envelope.left
      (And.intro envelope.right.left
        (And.intro provenanceUnary'
          (And.intro envelope.right.right.right.left
            (And.intro classifierUnary'
              (And.intro provenanceRow'
                (And.intro classifierRow (And.intro classifierReadback' pkgSig'))))))))
    sameClassifier

end BEDC.Derived.CurvatureUp
