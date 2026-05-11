import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem CurvatureBracketCarrier_chernweil_export_dependency_surface [AskSetup]
    [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger derham exportProvenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA
        ledgerB boundary curvatureLedger ->
      UnaryHistory derham ->
        UnaryHistory connectionLedger ->
          Cont curvatureLedger derham exportProvenance ->
            Cont exportProvenance connectionLedger classifier ->
              PkgSig bundle classifier pkg ->
                CurvatureChernWeilSourceEnvelope curvatureLedger derham exportProvenance
                    connectionLedger classifier bundle pkg ∧
                  hsame classifier (append (append curvatureLedger derham) connectionLedger) ∧
                    UnaryHistory curvatureLedger := by
  intro carrier derhamUnary connectionLedgerUnary exportRow classifierRow pkgSig
  have coverage :=
    CurvatureChernWeilSourceEnvelope_coverage carrier derhamUnary connectionLedgerUnary
      exportRow classifierRow pkgSig
  have boundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  exact And.intro coverage.left (And.intro coverage.right boundaryRows.right.left)

theorem CurvatureChernWeilSourceEnvelope_source_envelope_row [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger derham provenanceCW connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      UnaryHistory derham ->
        UnaryHistory connectionLedger ->
          Cont curvatureLedger derham provenanceCW ->
            Cont provenanceCW connectionLedger classifier ->
              PkgSig bundle classifier pkg ->
                UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
                  CurvatureChernWeilSourceEnvelope curvatureLedger derham provenanceCW
                    connectionLedger classifier bundle pkg ∧
                    hsame classifier
                      (append (append curvatureLedger derham) connectionLedger) := by
  intro carrier derhamUnary connectionLedgerUnary provenanceRow classifierRow pkgSig
  have boundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  have coverage :=
    CurvatureChernWeilSourceEnvelope_coverage carrier derhamUnary connectionLedgerUnary
      provenanceRow classifierRow pkgSig
  exact And.intro boundaryRows.left
    (And.intro boundaryRows.right.left (And.intro coverage.left coverage.right))

theorem CurvatureChernWeilSourceEnvelope_status_record [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB boundary
      curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger classifier
          bundle pkg ->
        SemanticNameCert
            (fun row : BHist =>
              CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                connectionLedger row bundle pkg)
            (fun row : BHist =>
              CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                connectionLedger row bundle pkg)
            (fun row : BHist =>
              CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                connectionLedger row bundle pkg)
            (fun left right : BHist =>
              CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                  connectionLedger left bundle pkg ∧
                CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                  connectionLedger right bundle pkg ∧
                  hsame left right) ∧
          UnaryHistory curvatureLedger ∧ Cont curvatureLedger derham provenance ∧
            Cont provenance connectionLedger classifier ∧ PkgSig bundle classifier pkg := by
  intro carrier envelope
  have carrierRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
              connectionLedger row bundle pkg)
          (fun row : BHist =>
            CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
              connectionLedger row bundle pkg)
          (fun row : BHist =>
            CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
              connectionLedger row bundle pkg)
          (fun left right : BHist =>
            CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                connectionLedger left bundle pkg ∧
              CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance
                connectionLedger right bundle pkg ∧
                hsame left right) := {
    core := {
      carrier_inhabited := Exists.intro classifier envelope
      equiv_refl := by
        intro row rowEnvelope
        exact And.intro rowEnvelope (And.intro rowEnvelope (hsame_refl row))
      equiv_symm := by
        intro left right related
        exact And.intro related.right.left
          (And.intro related.left (hsame_symm related.right.right))
      equiv_trans := by
        intro left middle right relatedLM relatedMR
        exact And.intro relatedLM.left
          (And.intro relatedMR.right.left
            (hsame_trans relatedLM.right.right relatedMR.right.right))
      carrier_respects_equiv := by
        intro _left _right related _leftEnvelope
        exact related.right.left
    }
    pattern_sound := by
      intro _row rowEnvelope
      exact rowEnvelope
    ledger_sound := by
      intro _row rowEnvelope
      exact rowEnvelope
  }
  exact And.intro cert
    (And.intro carrierRows.right.left
      (And.intro envelope.right.right.right.right.right.left
        (And.intro envelope.right.right.right.right.right.right.left
          envelope.right.right.right.right.right.right.right.right)))

end BEDC.Derived.CurvatureUp
