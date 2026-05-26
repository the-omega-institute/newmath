import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionCarrier_real_seal_public_boundary [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      handoffRead realSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont values ledger handoffRead ->
        Cont handoffRead route realSeal ->
          Cont realSeal nameRow publicRead ->
            PkgSig bundle realSeal pkg ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory handoffRead ∧ UnaryHistory realSeal ∧ UnaryHistory publicRead ∧
                  Cont values ledger handoffRead ∧ Cont handoffRead route realSeal ∧
                    Cont realSeal nameRow publicRead ∧ PkgSig bundle nameRow pkg ∧
                      PkgSig bundle realSeal pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier valuesLedgerHandoff handoffRouteReal realNamePublic realSealPkg publicPkg
  obtain ⟨_partitionUnary, _cellsUnary, valuesUnary, _readsUnary, _refinementUnary,
    _endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed valuesUnary ledgerUnary valuesLedgerHandoff
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed handoffUnary routeUnary handoffRouteReal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realSealUnary nameRowUnary realNamePublic
  exact
    ⟨handoffUnary, realSealUnary, publicUnary, valuesLedgerHandoff, handoffRouteReal,
      realNamePublic, nameRowPkg, realSealPkg, publicPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
