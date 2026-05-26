import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionCarrier_scoped_obligation_package [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      commonCell endpointRead valueRead handoffRead realRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont cells refinement commonCell ->
        Cont commonCell endpointLedger endpointRead ->
          Cont endpointLedger values valueRead ->
            hsame endpointRead valueRead ->
              Cont values ledger handoffRead ->
                Cont handoffRead route realRead ->
                  Cont ledger route realSeal ->
                    PkgSig bundle realRead pkg ->
                      PkgSig bundle realSeal pkg ->
                        UnaryHistory commonCell ∧ UnaryHistory endpointRead ∧
                          UnaryHistory valueRead ∧ UnaryHistory handoffRead ∧
                            UnaryHistory realRead ∧ UnaryHistory realSeal ∧
                              Cont cells refinement commonCell ∧
                                Cont commonCell endpointLedger endpointRead ∧
                                  Cont endpointLedger values valueRead ∧
                                    hsame endpointRead valueRead ∧
                                      Cont values ledger handoffRead ∧
                                        Cont handoffRead route realRead ∧
                                          Cont ledger route realSeal ∧
                                            PkgSig bundle nameRow pkg ∧
                                              PkgSig bundle realRead pkg ∧
                                                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory Cont PkgSig
  intro carrier cellsCommon commonEndpoint endpointValue sameEndpointValue valuesHandoff
    handoffReal ledgerReal realPkg sealPkg
  obtain ⟨_partitionUnary, cellsUnary, valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have commonCellUnary : UnaryHistory commonCell :=
    unary_cont_closed cellsUnary refinementUnary cellsCommon
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed commonCellUnary endpointLedgerUnary commonEndpoint
  have valueReadUnary : UnaryHistory valueRead :=
    unary_cont_closed endpointLedgerUnary valuesUnary endpointValue
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed valuesUnary ledgerUnary valuesHandoff
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed handoffReadUnary routeUnary handoffReal
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed ledgerUnary routeUnary ledgerReal
  exact
    ⟨commonCellUnary, endpointReadUnary, valueReadUnary, handoffReadUnary, realReadUnary,
      realSealUnary, cellsCommon, commonEndpoint, endpointValue, sameEndpointValue,
      valuesHandoff, handoffReal, ledgerReal, nameRowPkg, realPkg, sealPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
