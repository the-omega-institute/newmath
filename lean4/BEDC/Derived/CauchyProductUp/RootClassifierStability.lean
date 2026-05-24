import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_classifier_stability [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name sourceA' sourceB' windowA' windowB'
      radiusA' radiusB' observationA' observationB' product' classifier' transport'
      routes' ledger' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      hsame sourceA sourceA' ->
        hsame sourceB sourceB' ->
          hsame windowA windowA' ->
            hsame windowB windowB' ->
              hsame radiusA radiusA' ->
                hsame radiusB radiusB' ->
                  hsame observationA observationA' ->
                    hsame observationB observationB' ->
                      hsame product product' ->
                        hsame classifier classifier' ->
                          hsame transport transport' ->
                            hsame routes routes' ->
                              hsame ledger ledger' ->
                                PkgSig bundle name' pkg ->
                                  CauchyProductPacket sourceA' sourceB' windowA' windowB'
                                    radiusA' radiusB' observationA' observationB' product'
                                      classifier' transport' routes' ledger' name' bundle
                                        pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro packet sameSourceA sameSourceB sameWindowA sameWindowB sameRadiusA sameRadiusB
    sameObservationA sameObservationB sameProduct sameClassifier sameTransport sameRoutes
    sameLedger namePkg'
  cases sameSourceA
  cases sameSourceB
  cases sameWindowA
  cases sameWindowB
  cases sameRadiusA
  cases sameRadiusB
  cases sameObservationA
  cases sameObservationB
  cases sameProduct
  cases sameClassifier
  cases sameTransport
  cases sameRoutes
  cases sameLedger
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, _namePkg⟩ := packet
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, routesUnary, ledgerUnary, windowTransport,
      productRoute, classifierRoute, namePkg'⟩

theorem CauchyProductPacket_root_product_row_determinacy [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      product' classifier classifier' transport routes ledger name name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product' classifier' transport routes ledger name' bundle pkg ->
        hsame product product' ∧ hsame classifier classifier' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro leftPacket rightPacket
  obtain ⟨_leftSourceAUnary, _leftSourceBUnary, _leftWindowAUnary, _leftWindowBUnary,
    _leftRadiusAUnary, _leftRadiusBUnary, _leftObservationAUnary, _leftObservationBUnary,
    _leftRoutesUnary, _leftLedgerUnary, _leftWindowTransport, leftProductRoute,
    leftClassifierRoute, _leftNamePkg⟩ := leftPacket
  obtain ⟨_rightSourceAUnary, _rightSourceBUnary, _rightWindowAUnary, _rightWindowBUnary,
    _rightRadiusAUnary, _rightRadiusBUnary, _rightObservationAUnary,
    _rightObservationBUnary, _rightRoutesUnary, _rightLedgerUnary, _rightWindowTransport,
    rightProductRoute, rightClassifierRoute, _rightNamePkg⟩ := rightPacket
  have sameProduct : hsame product product' :=
    cont_deterministic leftProductRoute rightProductRoute
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameProduct (hsame_refl ledger) leftClassifierRoute
      rightClassifierRoute
  exact ⟨sameProduct, sameClassifier⟩

end BEDC.Derived.CauchyProductUp
