import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budgeted_bilinear_diagonal [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB productAB
      classifierAB transportAB routesAB ledgerAB nameAB sourceC sourceD windowC windowD radiusC
      radiusD observationC observationD productCD classifierCD transportCD routesCD ledgerCD nameCD
      budgetClassifier budgetSeal diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB productAB classifierAB transportAB routesAB ledgerAB nameAB bundle pkg ->
      CauchyProductPacket sourceC sourceD windowC windowD radiusC radiusD observationC
          observationD productCD classifierCD transportCD routesCD ledgerCD nameCD bundle pkg ->
        Cont classifierAB routesAB budgetClassifier ->
          Cont classifierCD routesCD budgetClassifier ->
            Cont budgetClassifier ledgerAB budgetSeal ->
              Cont budgetSeal routesAB diagonalRead ->
                PkgSig bundle diagonalRead pkg ->
                  UnaryHistory productAB ∧ UnaryHistory productCD ∧
                    UnaryHistory classifierAB ∧ UnaryHistory classifierCD ∧
                      UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                        UnaryHistory diagonalRead ∧ Cont observationA observationB productAB ∧
                          Cont observationC observationD productCD ∧
                            Cont productAB ledgerAB classifierAB ∧
                              Cont productCD ledgerCD classifierCD ∧
                                Cont classifierAB routesAB budgetClassifier ∧
                                  Cont classifierCD routesCD budgetClassifier ∧
                                    Cont budgetClassifier ledgerAB budgetSeal ∧
                                      Cont budgetSeal routesAB diagonalRead ∧
                                        PkgSig bundle nameAB pkg ∧ PkgSig bundle nameCD pkg ∧
                                          PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packetAB packetCD classifierABBudget classifierCDBudget budgetSealRoute diagonalRoute
    diagonalPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesABUnary, ledgerABUnary,
    _transportABRoute, productABRoute, classifierABRoute, nameABPkg⟩ := packetAB
  obtain ⟨_sourceCUnary, _sourceDUnary, _windowCUnary, _windowDUnary, _radiusCUnary,
    _radiusDUnary, observationCUnary, observationDUnary, _routesCDUnary, ledgerCDUnary,
    _transportCDRoute, productCDRoute, classifierCDRoute, nameCDPkg⟩ := packetCD
  have productABUnary : UnaryHistory productAB :=
    unary_cont_closed observationAUnary observationBUnary productABRoute
  have productCDUnary : UnaryHistory productCD :=
    unary_cont_closed observationCUnary observationDUnary productCDRoute
  have classifierABUnary : UnaryHistory classifierAB :=
    unary_cont_closed productABUnary ledgerABUnary classifierABRoute
  have classifierCDUnary : UnaryHistory classifierCD :=
    unary_cont_closed productCDUnary ledgerCDUnary classifierCDRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierABUnary routesABUnary classifierABBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerABUnary budgetSealRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed budgetSealUnary routesABUnary diagonalRoute
  exact
    ⟨productABUnary, productCDUnary, classifierABUnary, classifierCDUnary,
      budgetClassifierUnary, budgetSealUnary, diagonalReadUnary, productABRoute,
      productCDRoute, classifierABRoute, classifierCDRoute, classifierABBudget,
      classifierCDBudget, budgetSealRoute, diagonalRoute, nameABPkg, nameCDPkg,
      diagonalPkg⟩

end BEDC.Derived.CauchyProductUp
