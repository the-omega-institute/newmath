import BEDC.Derived.CauchyProductUp
import BEDC.Derived.RealseriesUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.Derived.RealseriesUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_realseries_shared_selector_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name seriesTerm seriesPartial seriesTail seriesWindow
      seriesReadback seriesDyadic seriesTransport seriesReplay seriesProvenance seriesCert
      sharedBudget productSeal seriesSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      RealSeriesRootCauchyProductSurface seriesTerm seriesPartial seriesTail seriesReadback
        seriesDyadic sharedBudget seriesTransport seriesReplay seriesProvenance seriesCert bundle pkg ->
        Cont classifier routes productSeal ->
          Cont seriesTail seriesWindow seriesReadback ->
            Cont seriesReadback sharedBudget seriesSeal ->
              PkgSig bundle seriesSeal pkg ->
                UnaryHistory productSeal ∧ UnaryHistory seriesReadback ∧
                  UnaryHistory seriesSeal ∧ Cont classifier routes productSeal ∧
                    Cont seriesTail seriesWindow seriesReadback ∧
                      Cont seriesReadback sharedBudget seriesSeal ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle seriesSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet seriesSurface classifierProductSeal seriesReadbackRoute seriesSealRoute
    seriesSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  obtain ⟨_seriesTermUnary, _seriesPartialUnary, seriesTailUnary, seriesReadbackUnary,
    _seriesDyadicUnary, sharedBudgetUnary, _seriesTransportUnary, _seriesReplayUnary,
    _seriesProvenanceUnary, _seriesCertUnary, _readbackBudgetThreshold,
    _seriesProvenancePkg⟩ := seriesSurface
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed classifierUnary routesUnary classifierProductSeal
  have seriesWindowUnary : UnaryHistory seriesWindow :=
    (unary_cont_factors_from_result seriesReadbackRoute seriesReadbackUnary).right
  have seriesReadbackUnary' : UnaryHistory seriesReadback :=
    unary_cont_closed seriesTailUnary seriesWindowUnary seriesReadbackRoute
  have seriesSealUnary : UnaryHistory seriesSeal :=
    unary_cont_closed seriesReadbackUnary' sharedBudgetUnary seriesSealRoute
  exact
    ⟨productSealUnary, seriesReadbackUnary', seriesSealUnary, classifierProductSeal,
      seriesReadbackRoute, seriesSealRoute, namePkg, seriesSealPkg⟩

end BEDC.Derived.CauchyProductUp
