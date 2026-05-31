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

theorem CauchyProductPacket_public_real_series_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name productSeal publicRead seriesTerm seriesPartial
      seriesWindow seriesReadback seriesDyadic seriesThreshold seriesTransport seriesReplay
      seriesProvenance seriesCert seriesSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      RealSeriesRootCauchyProductSurface seriesTerm seriesPartial seriesWindow seriesReadback
        seriesDyadic seriesThreshold seriesTransport seriesReplay seriesProvenance seriesCert
        bundle pkg ->
        Cont classifier routes productSeal ->
          Cont productSeal ledger publicRead ->
            Cont seriesReadback seriesThreshold seriesSeal ->
              PkgSig bundle publicRead pkg ->
                PkgSig bundle seriesSeal pkg ->
                  UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory productSeal ∧
                    UnaryHistory publicRead ∧ UnaryHistory seriesSeal ∧
                      Cont product ledger classifier ∧ Cont classifier routes productSeal ∧
                        Cont productSeal ledger publicRead ∧
                          Cont seriesReadback seriesThreshold seriesSeal ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg ∧
                              PkgSig bundle seriesSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet seriesSurface classifierProductSeal productSealPublic seriesSealRoute publicPkg
    seriesSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  obtain ⟨_seriesTermUnary, _seriesPartialUnary, _seriesWindowUnary, seriesReadbackUnary,
    _seriesDyadicUnary, seriesThresholdUnary, _seriesTransportUnary, _seriesReplayUnary,
    _seriesProvenanceUnary, _seriesCertUnary, _readbackDyadicThreshold,
    _seriesProvenancePkg⟩ := seriesSurface
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed classifierUnary routesUnary classifierProductSeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed productSealUnary ledgerUnary productSealPublic
  have seriesSealUnary : UnaryHistory seriesSeal :=
    unary_cont_closed seriesReadbackUnary seriesThresholdUnary seriesSealRoute
  exact
    ⟨productUnary, classifierUnary, productSealUnary, publicReadUnary, seriesSealUnary,
      classifierRoute, classifierProductSeal, productSealPublic, seriesSealRoute, namePkg,
      publicPkg, seriesSealPkg⟩

end BEDC.Derived.CauchyProductUp
