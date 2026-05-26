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

theorem CauchyProductPacket_public_real_series_budget_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal seriesTerm seriesPartial
      seriesWindow seriesReadback seriesDyadic seriesThreshold seriesTransport seriesReplay
      seriesProvenance seriesCert seriesSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      RealSeriesRootCauchyProductSurface seriesTerm seriesPartial seriesWindow seriesReadback
        seriesDyadic seriesThreshold seriesTransport seriesReplay seriesProvenance seriesCert
        bundle pkg ->
        Cont classifier routes budgetClassifier ->
          Cont budgetClassifier ledger budgetSeal ->
            Cont budgetSeal routes seriesTerm ->
              Cont seriesReadback seriesThreshold seriesSeal ->
                PkgSig bundle seriesSeal pkg ->
                  UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                    UnaryHistory seriesTerm ∧ UnaryHistory seriesReadback ∧
                      UnaryHistory seriesSeal ∧ Cont classifier routes budgetClassifier ∧
                        Cont budgetClassifier ledger budgetSeal ∧
                          Cont budgetSeal routes seriesTerm ∧
                            Cont seriesReadback seriesThreshold seriesSeal ∧
                              PkgSig bundle seriesSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet seriesSurface classifierBudget budgetSealRoute budgetSeriesTerm seriesSealRoute
    seriesSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, _namePkg⟩ := packet
  obtain ⟨_seriesTermUnary, _seriesPartialUnary, _seriesWindowUnary, seriesReadbackUnary,
    _seriesDyadicUnary, seriesThresholdUnary, _seriesTransportUnary, _seriesReplayUnary,
    _seriesProvenanceUnary, _seriesCertUnary, _readbackDyadicThreshold,
    _seriesProvenancePkg⟩ := seriesSurface
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have seriesTermUnary' : UnaryHistory seriesTerm :=
    unary_cont_closed budgetSealUnary routesUnary budgetSeriesTerm
  have seriesSealUnary : UnaryHistory seriesSeal :=
    unary_cont_closed seriesReadbackUnary seriesThresholdUnary seriesSealRoute
  exact
    ⟨budgetClassifierUnary, budgetSealUnary, seriesTermUnary', seriesReadbackUnary,
      seriesSealUnary, classifierBudget, budgetSealRoute, budgetSeriesTerm,
      seriesSealRoute, seriesSealPkg⟩

end BEDC.Derived.CauchyProductUp
