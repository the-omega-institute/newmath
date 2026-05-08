import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureChernWeilSourceEnvelope_derham_transport_readback [AskSetup] [PackageSetup]
    {curvatureLedger derham derham' provenance provenance' connectionLedger classifier
      classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
        classifier bundle pkg ->
      hsame derham derham' ->
        Cont curvatureLedger derham' provenance' ->
          Cont provenance' connectionLedger classifier' ->
            PkgSig bundle classifier' pkg ->
              CurvatureChernWeilSourceEnvelope curvatureLedger derham' provenance'
                    connectionLedger classifier' bundle pkg ∧
                hsame provenance provenance' ∧
                  hsame classifier classifier' ∧
                    hsame classifier'
                      (append (append curvatureLedger derham') connectionLedger) := by
  intro envelope sameDerham provenanceCont' classifierCont' pkgSig'
  have derhamUnary' : UnaryHistory derham' :=
    unary_transport envelope.right.left sameDerham
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed envelope.left derhamUnary' provenanceCont'
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed provenanceUnary' envelope.right.right.right.left classifierCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame (hsame_refl curvatureLedger) sameDerham
      envelope.right.right.right.right.right.left provenanceCont'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameProvenance (hsame_refl connectionLedger)
      envelope.right.right.right.right.right.right.left classifierCont'
  have classifierReadback' :
      hsame classifier' (append (append curvatureLedger derham') connectionLedger) :=
    hsame_trans classifierCont'
      (congrArg (fun row : BHist => append row connectionLedger) provenanceCont')
  have envelope' :
      CurvatureChernWeilSourceEnvelope curvatureLedger derham' provenance' connectionLedger
        classifier' bundle pkg :=
    And.intro envelope.left
      (And.intro derhamUnary'
        (And.intro provenanceUnary'
          (And.intro envelope.right.right.right.left
            (And.intro classifierUnary'
              (And.intro provenanceCont'
                (And.intro classifierCont'
                  (And.intro classifierReadback' pkgSig')))))))
  exact And.intro envelope'
    (And.intro sameProvenance
      (And.intro sameClassifier classifierReadback'))

end BEDC.Derived.CurvatureUp
