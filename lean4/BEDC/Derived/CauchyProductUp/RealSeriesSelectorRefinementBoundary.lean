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

theorem CauchyProductPacket_realseries_selector_refinement_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name term partialRow seriesWindow readback dyadic
      threshold seriesTransport replay provenance cert productSeal seriesEndpoint
      refinedProductSeal refinedSeriesEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      RealSeriesRootCauchyProductSurface term partialRow seriesWindow readback dyadic threshold
        seriesTransport replay provenance cert bundle pkg ->
        Cont classifier routes productSeal ->
          Cont threshold cert seriesEndpoint ->
            hsame productSeal refinedProductSeal ->
              hsame seriesEndpoint refinedSeriesEndpoint ->
                PkgSig bundle refinedProductSeal pkg ->
                  PkgSig bundle refinedSeriesEndpoint pkg ->
                    UnaryHistory refinedProductSeal ∧ UnaryHistory refinedSeriesEndpoint ∧
                      hsame productSeal refinedProductSeal ∧
                        hsame seriesEndpoint refinedSeriesEndpoint ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle refinedProductSeal pkg ∧
                            PkgSig bundle refinedSeriesEndpoint pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet seriesSurface productSealRoute seriesEndpointRoute sameProduct sameSeries
    refinedProductPkg refinedSeriesPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  obtain ⟨_termUnary, _partialUnary, _seriesWindowUnary, _readbackUnary, _dyadicUnary,
    thresholdUnary, _seriesTransportUnary, _replayUnary, _provenanceUnary, certUnary,
    _readbackThresholdRoute, _provenancePkg⟩ := seriesSurface
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed classifierUnary routesUnary productSealRoute
  have refinedProductUnary : UnaryHistory refinedProductSeal :=
    unary_transport productSealUnary sameProduct
  have seriesEndpointUnary : UnaryHistory seriesEndpoint :=
    unary_cont_closed thresholdUnary certUnary seriesEndpointRoute
  have refinedSeriesUnary : UnaryHistory refinedSeriesEndpoint :=
    unary_transport seriesEndpointUnary sameSeries
  exact
    ⟨refinedProductUnary, refinedSeriesUnary, sameProduct, sameSeries, namePkg,
      refinedProductPkg, refinedSeriesPkg⟩

end BEDC.Derived.CauchyProductUp
