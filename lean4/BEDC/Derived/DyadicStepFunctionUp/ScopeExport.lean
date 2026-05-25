import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionCarrier_scope_export [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      scopeRead regseqRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg →
      Cont ledger route scopeRead →
        Cont values ledger regseqRead →
          Cont regseqRead route realSeal →
            UnaryHistory partition ∧ UnaryHistory cells ∧ UnaryHistory values ∧
              UnaryHistory refinement ∧ UnaryHistory endpointLedger ∧ UnaryHistory ledger ∧
                UnaryHistory scopeRead ∧ UnaryHistory regseqRead ∧ UnaryHistory realSeal ∧
                  Cont partition cells values ∧ Cont refinement endpointLedger ledger ∧
                    Cont ledger route scopeRead ∧ Cont values ledger regseqRead ∧
                      Cont regseqRead route realSeal ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier ledgerRouteScope valuesLedgerRegseq regseqRouteReal
  obtain ⟨partitionUnary, cellsUnary, valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    partitionCellsValues, _valuesReadsRefinement, refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteScope
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed valuesUnary ledgerUnary valuesLedgerRegseq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary routeUnary regseqRouteReal
  exact
    ⟨partitionUnary, cellsUnary, valuesUnary, refinementUnary, endpointLedgerUnary,
      ledgerUnary, scopeUnary, regseqUnary, realSealUnary, partitionCellsValues,
      refinementEndpointLedger, ledgerRouteScope, valuesLedgerRegseq, regseqRouteReal,
      nameRowPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
