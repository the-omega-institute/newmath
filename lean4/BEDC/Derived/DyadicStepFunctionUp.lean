import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicStepFunctionPacket [AskSetup] [PackageSetup]
    (partition cells values classifier refinement endpoints ledger route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory partition ∧ UnaryHistory cells ∧ UnaryHistory values ∧
    UnaryHistory classifier ∧ UnaryHistory refinement ∧ UnaryHistory endpoints ∧
      UnaryHistory ledger ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont partition cells values ∧
          Cont refinement endpoints ledger ∧ hsame classifier ledger ∧
            PkgSig bundle provenance pkg

theorem DyadicStepFunctionPacket_refinement_stability [AskSetup] [PackageSetup]
    {partition cells values classifier refinement endpoints ledger route provenance nameCert
      partition' cells' values' classifier' refinement' endpoints' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionPacket partition cells values classifier refinement endpoints ledger route
        provenance nameCert bundle pkg ->
      hsame partition partition' ->
        hsame cells cells' ->
          hsame values values' ->
            hsame classifier classifier' ->
              hsame refinement refinement' ->
                hsame endpoints endpoints' ->
                  hsame ledger ledger' ->
                    Cont partition' cells' values' ->
                      Cont refinement' endpoints' ledger' ->
                        DyadicStepFunctionPacket partition' cells' values' classifier'
                          refinement' endpoints' ledger' route provenance nameCert bundle pkg := by
  intro packet samePartition sameCells sameValues sameClassifier sameRefinement sameEndpoints
    sameLedger refinedValueRow refinedLedgerRow
  rcases packet with
    ⟨partitionUnary, cellsUnary, valuesUnary, classifierUnary, refinementUnary, endpointsUnary,
      ledgerUnary, routeUnary, provenanceUnary, nameCertUnary, _valueRow, _ledgerRow,
      classifierLedger, provenancePkg⟩
  have partitionUnary' : UnaryHistory partition' :=
    unary_transport partitionUnary samePartition
  have cellsUnary' : UnaryHistory cells' :=
    unary_transport cellsUnary sameCells
  have valuesUnary' : UnaryHistory values' :=
    unary_transport valuesUnary sameValues
  have classifierUnary' : UnaryHistory classifier' :=
    unary_transport classifierUnary sameClassifier
  have refinementUnary' : UnaryHistory refinement' :=
    unary_transport refinementUnary sameRefinement
  have endpointsUnary' : UnaryHistory endpoints' :=
    unary_transport endpointsUnary sameEndpoints
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have classifierLedger' : hsame classifier' ledger' :=
    hsame_trans (hsame_symm sameClassifier) (hsame_trans classifierLedger sameLedger)
  exact
    ⟨partitionUnary', cellsUnary', valuesUnary', classifierUnary', refinementUnary',
      endpointsUnary', ledgerUnary', routeUnary, provenanceUnary, nameCertUnary,
      refinedValueRow, refinedLedgerRow, classifierLedger', provenancePkg⟩

end BEDC.Derived.DyadicStepFunctionUp
