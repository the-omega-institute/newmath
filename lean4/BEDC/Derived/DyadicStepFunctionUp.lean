import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def DyadicStepFunctionCarrier [AskSetup] [PackageSetup]
    (partition cells values reads refinement endpointLedger ledger route provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory partition ∧ UnaryHistory cells ∧ UnaryHistory values ∧ UnaryHistory reads ∧
    UnaryHistory refinement ∧ UnaryHistory endpointLedger ∧ UnaryHistory ledger ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont partition cells values ∧ Cont values reads refinement ∧
          Cont refinement endpointLedger ledger ∧ Cont route provenance nameRow ∧
            PkgSig bundle nameRow pkg

theorem DyadicStepFunctionCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont ledger route exported ->
        UnaryHistory exported ∧ UnaryHistory ledger ∧ Cont refinement endpointLedger ledger ∧
          Cont ledger route exported ∧ PkgSig bundle nameRow pkg := by
  intro carrier exportedRoute
  obtain ⟨_partitionUnary, _cellsUnary, _valuesUnary, _readsUnary, _refinementUnary,
    _endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerUnary routeUnary exportedRoute
  exact
    ⟨exportedUnary, ledgerUnary, refinementEndpointLedger, exportedRoute, nameRowPkg⟩

theorem DyadicStepFunctionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger
            route provenance nameRow bundle pkg ∧ hsame row nameRow)
        (fun _row : BHist =>
          DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger
            route provenance nameRow bundle pkg ∧ Cont partition cells values ∧
              Cont refinement endpointLedger ledger ∧ Cont route provenance nameRow)
        (fun row : BHist => PkgSig bundle nameRow pkg ∧ hsame row nameRow)
        hsame := by
  intro carrier
  have carrierPacket := carrier
  obtain ⟨_partitionUnary, _cellsUnary, _valuesUnary, _readsUnary, _refinementUnary,
    _endpointLedgerUnary, _ledgerUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    partitionCellsValues, _valuesReadsRefinement, refinementEndpointLedger,
    routeProvenanceNameRow, nameRowPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameRow (And.intro carrierPacket (hsame_refl nameRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, partitionCellsValues, refinementEndpointLedger,
          routeProvenanceNameRow⟩
    ledger_sound := by
      intro _row source
      exact ⟨nameRowPkg, source.right⟩
  }

theorem DyadicStepFunctionCarrier_endpoint_value_transport_determinacy [AskSetup]
    [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      endpointRead valueRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg →
      Cont endpointLedger values endpointRead →
        Cont values reads valueRead →
          hsame endpointRead valueRead →
            UnaryHistory endpointRead ∧ UnaryHistory valueRead ∧
              Cont endpointLedger values endpointRead ∧ Cont values reads valueRead ∧
                hsame endpointRead valueRead ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier endpointValueRead valueReadRow sameRead
  obtain ⟨_partitionUnary, _cellsUnary, valuesUnary, readsUnary, _refinementUnary,
    endpointLedgerUnary, _ledgerUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointLedgerUnary valuesUnary endpointValueRead
  have valueReadUnary : UnaryHistory valueRead :=
    unary_cont_closed valuesUnary readsUnary valueReadRow
  exact
    ⟨endpointReadUnary, valueReadUnary, endpointValueRead, valueReadRow, sameRead,
      nameRowPkg⟩

theorem DyadicStepFunctionCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      handoffRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont values ledger handoffRead ->
        Cont handoffRead route realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory partition ∧ UnaryHistory values ∧ UnaryHistory ledger ∧
              UnaryHistory handoffRead ∧ UnaryHistory realRead ∧
                Cont values ledger handoffRead ∧ Cont handoffRead route realRead ∧
                  PkgSig bundle nameRow pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier valuesLedgerHandoff handoffRouteReal realReadPkg
  obtain ⟨partitionUnary, _cellsUnary, valuesUnary, _readsUnary, _refinementUnary,
    _endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed valuesUnary ledgerUnary valuesLedgerHandoff
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed handoffReadUnary routeUnary handoffRouteReal
  exact
    ⟨partitionUnary, valuesUnary, ledgerUnary, handoffReadUnary, realReadUnary,
      valuesLedgerHandoff, handoffRouteReal, nameRowPkg, realReadPkg⟩

theorem DyadicStepFunctionCarrier_real_seal_window_exactness [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont ledger route realSeal ->
        PkgSig bundle nameRow pkg ->
          UnaryHistory cells ∧ UnaryHistory values ∧ UnaryHistory endpointLedger ∧
            UnaryHistory ledger ∧ UnaryHistory realSeal ∧ Cont partition cells values ∧
              Cont refinement endpointLedger ledger ∧ Cont ledger route realSeal ∧
                PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier ledgerRouteSeal nameRowPkg
  obtain ⟨_partitionUnary, cellsUnary, valuesUnary, _readsUnary, _refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    partitionCellsValues, _valuesReadsRefinement, refinementEndpointLedger,
    _routeProvenanceNameRow, _carrierNameRowPkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteSeal
  exact
    ⟨cellsUnary, valuesUnary, endpointLedgerUnary, ledgerUnary, realSealUnary,
      partitionCellsValues, refinementEndpointLedger, ledgerRouteSeal, nameRowPkg⟩

theorem DyadicStepFunctionCarrier_common_refinement_cell_coverage [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      commonCell endpointRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont cells refinement commonCell ->
        Cont commonCell endpointLedger endpointRead ->
          Cont endpointRead ledger consumerRead ->
            UnaryHistory cells ∧ UnaryHistory refinement ∧ UnaryHistory commonCell ∧
              UnaryHistory endpointRead ∧ UnaryHistory consumerRead ∧
                Cont cells refinement commonCell ∧
                  Cont commonCell endpointLedger endpointRead ∧
                    Cont endpointRead ledger consumerRead ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier cellsRefinementCommon commonEndpointRead endpointLedgerRead
  obtain ⟨_partitionUnary, cellsUnary, _valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
  have commonCellUnary : UnaryHistory commonCell :=
    unary_cont_closed cellsUnary refinementUnary cellsRefinementCommon
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed commonCellUnary endpointLedgerUnary commonEndpointRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointReadUnary ledgerUnary endpointLedgerRead
  exact
    ⟨cellsUnary, refinementUnary, commonCellUnary, endpointReadUnary, consumerReadUnary,
      cellsRefinementCommon, commonEndpointRead, endpointLedgerRead, nameRowPkg⟩

theorem DyadicStepFunctionCarrier_refinement_boundary_coverage [AskSetup] [PackageSetup]
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
                    UnaryHistory commonCell ∧ UnaryHistory endpointRead ∧
                      UnaryHistory consumerRead ∧ UnaryHistory regRead ∧
                        UnaryHistory realSeal ∧ UnaryHistory publicRead ∧
                          Cont cells refinement commonCell ∧
                            Cont commonCell endpointLedger endpointRead ∧
                              Cont endpointRead ledger consumerRead ∧ Cont ledger route regRead ∧
                                Cont regRead route realSeal ∧
                                  Cont consumerRead realSeal publicRead ∧
                                    PkgSig bundle nameRow pkg ∧
                                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier cellsRefinementCommon commonEndpointRead endpointLedgerRead ledgerRouteReg
    regRouteReal consumerRealPublic publicReadPkg
  obtain ⟨_partitionUnary, cellsUnary, _valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
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
  exact
    ⟨commonCellUnary, endpointReadUnary, consumerReadUnary, regReadUnary, realSealUnary,
      publicReadUnary, cellsRefinementCommon, commonEndpointRead, endpointLedgerRead,
      ledgerRouteReg, regRouteReal, consumerRealPublic, nameRowPkg, publicReadPkg⟩

theorem DyadicStepFunctionCarrier_product_closure [AskSetup] [PackageSetup]
    {partitionS cellsS valuesS readsS refinementS endpointLedgerS ledgerS routeS provenanceS
      nameRowS partitionT cellsT valuesT readsT refinementT endpointLedgerT ledgerT routeT
      provenanceT nameRowT productRead productSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partitionS cellsS valuesS readsS refinementS endpointLedgerS
        ledgerS routeS provenanceS nameRowS bundle pkg ->
      DyadicStepFunctionCarrier partitionT cellsT valuesT readsT refinementT endpointLedgerT
        ledgerT routeT provenanceT nameRowT bundle pkg ->
        Cont valuesS valuesT productRead ->
          Cont productRead ledgerS productSeal ->
            PkgSig bundle productSeal pkg ->
              UnaryHistory productRead ∧ UnaryHistory productSeal ∧
                Cont valuesS valuesT productRead ∧ Cont productRead ledgerS productSeal ∧
                  PkgSig bundle nameRowS pkg ∧ PkgSig bundle productSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrierS carrierT valuesProduct productLedgerSeal productSealPkg
  obtain ⟨_partitionSUnary, _cellsSUnary, valuesSUnary, _readsSUnary, _refinementSUnary,
    _endpointLedgerSUnary, ledgerSUnary, _routeSUnary, _provenanceSUnary, _nameRowSUnary,
    _partitionCellsValuesS, _valuesReadsRefinementS, _refinementEndpointLedgerS,
    _routeProvenanceNameRowS, nameRowSPkg⟩ := carrierS
  obtain ⟨_partitionTUnary, _cellsTUnary, valuesTUnary, _readsTUnary, _refinementTUnary,
    _endpointLedgerTUnary, _ledgerTUnary, _routeTUnary, _provenanceTUnary, _nameRowTUnary,
    _partitionCellsValuesT, _valuesReadsRefinementT, _refinementEndpointLedgerT,
    _routeProvenanceNameRowT, _nameRowTPkg⟩ := carrierT
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed valuesSUnary valuesTUnary valuesProduct
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed productReadUnary ledgerSUnary productLedgerSeal
  exact
    ⟨productReadUnary, productSealUnary, valuesProduct, productLedgerSeal, nameRowSPkg,
      productSealPkg⟩

theorem DyadicStepFunctionCarrier_refinement_intersection_closure [AskSetup] [PackageSetup]
    {partitionS cellsS valuesS readsS refinementS endpointLedgerS ledgerS routeS provenanceS
      nameRowS partitionT cellsT valuesT readsT refinementT endpointLedgerT ledgerT routeT
      provenanceT nameRowT intersectionCell endpointReadS endpointReadT mergedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partitionS cellsS valuesS readsS refinementS endpointLedgerS
        ledgerS routeS provenanceS nameRowS bundle pkg ->
      DyadicStepFunctionCarrier partitionT cellsT valuesT readsT refinementT endpointLedgerT
          ledgerT routeT provenanceT nameRowT bundle pkg ->
        Cont cellsS cellsT intersectionCell ->
          Cont intersectionCell endpointLedgerS endpointReadS ->
            Cont intersectionCell endpointLedgerT endpointReadT ->
              Cont endpointReadS endpointReadT mergedRead ->
                UnaryHistory intersectionCell ∧ UnaryHistory endpointReadS ∧
                  UnaryHistory endpointReadT ∧ UnaryHistory mergedRead ∧
                    Cont cellsS cellsT intersectionCell ∧
                      Cont intersectionCell endpointLedgerS endpointReadS ∧
                        Cont intersectionCell endpointLedgerT endpointReadT ∧
                          Cont endpointReadS endpointReadT mergedRead ∧
                            PkgSig bundle nameRowS pkg ∧ PkgSig bundle nameRowT pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrierS carrierT cellsIntersection intersectionEndpointS intersectionEndpointT
    endpointMerge
  obtain ⟨_partitionSUnary, cellsSUnary, _valuesSUnary, _readsSUnary, _refinementSUnary,
    endpointLedgerSUnary, _ledgerSUnary, _routeSUnary, _provenanceSUnary, _nameRowSUnary,
    _partitionCellsValuesS, _valuesReadsRefinementS, _refinementEndpointLedgerS,
    _routeProvenanceNameRowS, nameRowSPkg⟩ := carrierS
  obtain ⟨_partitionTUnary, cellsTUnary, _valuesTUnary, _readsTUnary, _refinementTUnary,
    endpointLedgerTUnary, _ledgerTUnary, _routeTUnary, _provenanceTUnary, _nameRowTUnary,
    _partitionCellsValuesT, _valuesReadsRefinementT, _refinementEndpointLedgerT,
    _routeProvenanceNameRowT, nameRowTPkg⟩ := carrierT
  have intersectionUnary : UnaryHistory intersectionCell :=
    unary_cont_closed cellsSUnary cellsTUnary cellsIntersection
  have endpointReadSUnary : UnaryHistory endpointReadS :=
    unary_cont_closed intersectionUnary endpointLedgerSUnary intersectionEndpointS
  have endpointReadTUnary : UnaryHistory endpointReadT :=
    unary_cont_closed intersectionUnary endpointLedgerTUnary intersectionEndpointT
  have mergedReadUnary : UnaryHistory mergedRead :=
    unary_cont_closed endpointReadSUnary endpointReadTUnary endpointMerge
  exact
    ⟨intersectionUnary, endpointReadSUnary, endpointReadTUnary, mergedReadUnary,
      cellsIntersection, intersectionEndpointS, intersectionEndpointT, endpointMerge,
      nameRowSPkg, nameRowTPkg⟩

theorem DyadicStepFunctionCarrier_window_obligations [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      commonCell endpointRead consumerRead regRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont cells refinement commonCell ->
        Cont commonCell endpointLedger endpointRead ->
          Cont endpointRead ledger consumerRead ->
            Cont ledger route regRead ->
              Cont regRead route realSeal ->
                PkgSig bundle realSeal pkg ->
                  UnaryHistory cells ∧ UnaryHistory commonCell ∧ UnaryHistory endpointRead ∧
                    UnaryHistory consumerRead ∧ UnaryHistory regRead ∧
                      UnaryHistory realSeal ∧ Cont cells refinement commonCell ∧
                        Cont commonCell endpointLedger endpointRead ∧
                          Cont endpointRead ledger consumerRead ∧ Cont ledger route regRead ∧
                            Cont regRead route realSeal ∧ PkgSig bundle nameRow pkg ∧
                              PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier cellsRefinementCommon commonEndpointRead endpointLedgerRead ledgerRouteReg
    regRouteReal realSealPkg
  obtain ⟨_partitionUnary, cellsUnary, _valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, nameRowPkg⟩ := carrier
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
  exact
    ⟨cellsUnary, commonCellUnary, endpointReadUnary, consumerReadUnary, regReadUnary,
      realSealUnary, cellsRefinementCommon, commonEndpointRead, endpointLedgerRead,
      ledgerRouteReg, regRouteReal, nameRowPkg, realSealPkg⟩

theorem DyadicStepFunctionCarrier_cellwise_sum_closure [AskSetup] [PackageSetup]
    {partitionS cellsS valuesS readsS refinementS endpointLedgerS ledgerS routeS provenanceS
      nameRowS partitionT cellsT valuesT readsT refinementT endpointLedgerT ledgerT routeT
      provenanceT nameRowT sumRead sumSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partitionS cellsS valuesS readsS refinementS endpointLedgerS
        ledgerS routeS provenanceS nameRowS bundle pkg ->
      DyadicStepFunctionCarrier partitionT cellsT valuesT readsT refinementT endpointLedgerT
        ledgerT routeT provenanceT nameRowT bundle pkg ->
        Cont valuesS valuesT sumRead ->
          Cont sumRead ledgerS sumSeal ->
            PkgSig bundle sumSeal pkg ->
              UnaryHistory sumRead ∧ UnaryHistory sumSeal ∧
                Cont valuesS valuesT sumRead ∧ Cont sumRead ledgerS sumSeal ∧
                  PkgSig bundle nameRowS pkg ∧ PkgSig bundle sumSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrierS carrierT valuesSum sumLedgerSeal sumSealPkg
  obtain ⟨_partitionSUnary, _cellsSUnary, valuesSUnary, _readsSUnary, _refinementSUnary,
    _endpointLedgerSUnary, ledgerSUnary, _routeSUnary, _provenanceSUnary, _nameRowSUnary,
    _partitionCellsValuesS, _valuesReadsRefinementS, _refinementEndpointLedgerS,
    _routeProvenanceNameRowS, nameRowSPkg⟩ := carrierS
  obtain ⟨_partitionTUnary, _cellsTUnary, valuesTUnary, _readsTUnary, _refinementTUnary,
    _endpointLedgerTUnary, _ledgerTUnary, _routeTUnary, _provenanceTUnary, _nameRowTUnary,
    _partitionCellsValuesT, _valuesReadsRefinementT, _refinementEndpointLedgerT,
    _routeProvenanceNameRowT, _nameRowTPkg⟩ := carrierT
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed valuesSUnary valuesTUnary valuesSum
  have sumSealUnary : UnaryHistory sumSeal :=
    unary_cont_closed sumReadUnary ledgerSUnary sumLedgerSeal
  exact
    ⟨sumReadUnary, sumSealUnary, valuesSum, sumLedgerSeal, nameRowSPkg, sumSealPkg⟩

theorem DyadicStepFunctionCarrier_stepwise_order_window [AskSetup] [PackageSetup]
    {partitionS cellsS valuesS readsS refinementS endpointLedgerS ledgerS routeS provenanceS
      nameRowS partitionT cellsT valuesT readsT refinementT endpointLedgerT ledgerT routeT
      provenanceT nameRowT orderRead orderSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partitionS cellsS valuesS readsS refinementS endpointLedgerS
        ledgerS routeS provenanceS nameRowS bundle pkg ->
      DyadicStepFunctionCarrier partitionT cellsT valuesT readsT refinementT endpointLedgerT
        ledgerT routeT provenanceT nameRowT bundle pkg ->
        Cont valuesS valuesT orderRead ->
          Cont orderRead ledgerT orderSeal ->
            PkgSig bundle orderSeal pkg ->
              UnaryHistory valuesS ∧ UnaryHistory valuesT ∧ UnaryHistory ledgerT ∧
                UnaryHistory orderRead ∧ UnaryHistory orderSeal ∧
                  Cont valuesS valuesT orderRead ∧ Cont orderRead ledgerT orderSeal ∧
                    PkgSig bundle nameRowS pkg ∧ PkgSig bundle nameRowT pkg ∧
                      PkgSig bundle orderSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrierS carrierT valuesOrder orderLedgerSeal orderSealPkg
  obtain ⟨_partitionSUnary, _cellsSUnary, valuesSUnary, _readsSUnary, _refinementSUnary,
    _endpointLedgerSUnary, _ledgerSUnary, _routeSUnary, _provenanceSUnary, _nameRowSUnary,
    _partitionCellsValuesS, _valuesReadsRefinementS, _refinementEndpointLedgerS,
    _routeProvenanceNameRowS, nameRowSPkg⟩ := carrierS
  obtain ⟨_partitionTUnary, _cellsTUnary, valuesTUnary, _readsTUnary, _refinementTUnary,
    _endpointLedgerTUnary, ledgerTUnary, _routeTUnary, _provenanceTUnary, _nameRowTUnary,
    _partitionCellsValuesT, _valuesReadsRefinementT, _refinementEndpointLedgerT,
    _routeProvenanceNameRowT, nameRowTPkg⟩ := carrierT
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed valuesSUnary valuesTUnary valuesOrder
  have orderSealUnary : UnaryHistory orderSeal :=
    unary_cont_closed orderReadUnary ledgerTUnary orderLedgerSeal
  exact
    ⟨valuesSUnary, valuesTUnary, ledgerTUnary, orderReadUnary, orderSealUnary,
      valuesOrder, orderLedgerSeal, nameRowSPkg, nameRowTPkg, orderSealPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
