import BEDC.Derived.ToposUp

namespace BEDC.Derived.ToposUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ToposFiniteCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint classifierEndpoint boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
        ledger provenance endpoint bundle pkg ->
      ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobjectClassifier
        ledger provenance classifierEndpoint bundle pkg ->
      hsame provenance classifierEndpoint ->
      Cont endpoint subobjectClassifier boundary ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          hsame ∧
        ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
          ledger classifierEndpoint endpoint bundle pkg ∧
          UnaryHistory boundary ∧ Cont category sheaf finiteLimit ∧
            Cont finiteLimit exponential subobjectClassifier ∧
              Cont ledger subobjectClassifier classifierEndpoint ∧
                Cont endpoint subobjectClassifier boundary ∧ PkgSig bundle endpoint pkg := by
  intro carrier ledgerRows sameProvenanceClassifier boundaryRow
  obtain ⟨transportedCarrier, categorySheafRow, finiteExponentialRow,
    _subobjectLedgerRow⟩ :=
    ToposFiniteCarrier_site_sheaf_classifier_obligation carrier ledgerRows
      sameProvenanceClassifier
  have transportedCarrierForOutput :
      ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
        ledger classifierEndpoint endpoint bundle pkg :=
    transportedCarrier
  obtain ⟨categoryUnary, sheafUnary, finiteLimitUnary, exponentialUnary, subobjectUnary,
    comparisonRow, ledgerRow, ledgerClassifierRow, endpointRow,
    packageRow⟩ := transportedCarrier
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed categoryUnary sheafUnary comparisonRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed finiteLimitUnary exponentialUnary ledgerRow
  have classifierEndpointUnary : UnaryHistory classifierEndpoint :=
    unary_cont_closed ledgerUnary subobjectUnary ledgerClassifierRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed comparisonUnary classifierEndpointUnary endpointRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed endpointUnary subobjectUnary boundaryRow
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
            comparison ledger provenance e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro transportedCarrierForOutput
      (And.intro boundaryUnary
        (And.intro categorySheafRow
          (And.intro finiteExponentialRow
            (And.intro ledgerClassifierRow (And.intro boundaryRow packageRow))))))

end BEDC.Derived.ToposUp
