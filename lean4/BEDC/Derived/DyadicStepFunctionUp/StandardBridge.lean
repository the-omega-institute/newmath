import BEDC.Derived.DyadicStepFunctionUp.PublicCertificate

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionUp_StdBridge [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      commonCell endpointRead consumerRead regRead realSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont cells refinement commonCell ->
        Cont commonCell endpointLedger endpointRead ->
          Cont endpointRead ledger consumerRead ->
            Cont ledger route regRead ->
              Cont regRead route realSeal ->
                Cont consumerRead realSeal publicRead ->
                  PkgSig bundle publicRead pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row publicRead ∧ Cont cells refinement commonCell ∧
                          Cont consumerRead realSeal publicRead)
                      (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                      hsame ∧
                      UnaryHistory publicRead ∧ Cont cells refinement commonCell ∧
                        Cont commonCell endpointLedger endpointRead ∧
                          Cont endpointRead ledger consumerRead ∧ Cont ledger route regRead ∧
                            Cont regRead route realSeal ∧
                              Cont consumerRead realSeal publicRead ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier cellsRefinementCommon commonEndpointRead endpointLedgerRead ledgerRouteReg
    regRouteReal consumerRealPublic publicReadPkg
  have carrierPacket := carrier
  obtain ⟨_partitionUnary, cellsUnary, _valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, _nameRowPkg⟩ := carrier
  have commonCellUnary : UnaryHistory commonCell :=
    unary_cont_closed cellsUnary refinementUnary cellsRefinementCommon
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed commonCellUnary endpointLedgerUnary commonEndpointRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointReadUnary ledgerUnary endpointLedgerRead
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteReg
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadUnary routeUnary regRouteReal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed consumerReadUnary realSealUnary consumerRealPublic
  have publicCert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row publicRead ∧ Cont cells refinement commonCell ∧
            Cont consumerRead realSeal publicRead)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame :=
    DyadicStepFunctionCarrier_public_certificate carrierPacket cellsRefinementCommon
      commonEndpointRead endpointLedgerRead ledgerRouteReg regRouteReal
      consumerRealPublic publicReadPkg
  exact
    ⟨publicCert, publicReadUnary, cellsRefinementCommon, commonEndpointRead,
      endpointLedgerRead, ledgerRouteReg, regRouteReal, consumerRealPublic, publicReadPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
