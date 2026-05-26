import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionCarrier_refinement_ledger_scope [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      endpointRead consumerRead regRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg →
      Cont endpointLedger ledger endpointRead →
        Cont endpointRead refinement consumerRead →
          Cont ledger route regRead →
            Cont regRead route realSeal →
              PkgSig bundle realSeal pkg →
                UnaryHistory refinement ∧ UnaryHistory endpointLedger ∧ UnaryHistory ledger ∧
                  UnaryHistory endpointRead ∧ UnaryHistory consumerRead ∧
                    UnaryHistory regRead ∧ UnaryHistory realSeal ∧
                      Cont endpointLedger ledger endpointRead ∧
                        Cont endpointRead refinement consumerRead ∧
                          Cont ledger route regRead ∧ Cont regRead route realSeal ∧
                            PkgSig bundle nameRow pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier endpointLedgerRead endpointRefinementConsumer ledgerRouteReg regRouteReal
    realSealPkg
  obtain ⟨_partitionUnary, _cellsUnary, _valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointLedgerUnary ledgerUnary endpointLedgerRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointReadUnary refinementUnary endpointRefinementConsumer
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteReg
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadUnary routeUnary regRouteReal
  exact
    ⟨refinementUnary, endpointLedgerUnary, ledgerUnary, endpointReadUnary, consumerReadUnary,
      regReadUnary, realSealUnary, endpointLedgerRead, endpointRefinementConsumer,
      ledgerRouteReg, regRouteReal, nameRowPkg, realSealPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
