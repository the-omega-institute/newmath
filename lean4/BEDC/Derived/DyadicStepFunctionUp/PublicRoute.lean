import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionCarrier_common_refinement_public_route [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      publicRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont endpointLedger values publicRead ->
        Cont publicRead route realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory publicRead ∧ UnaryHistory realRead ∧
              Cont endpointLedger values publicRead ∧ Cont publicRead route realRead ∧
                Cont refinement endpointLedger ledger ∧ PkgSig bundle nameRow pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointValuePublic publicRouteReal realReadPkg
  obtain ⟨_partitionUnary, _cellsUnary, valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, _ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointLedgerUnary valuesUnary endpointValuePublic
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed publicReadUnary routeUnary publicRouteReal
  exact
    ⟨publicReadUnary, realReadUnary, endpointValuePublic, publicRouteReal,
      refinementEndpointLedger, nameRowPkg, realReadPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
