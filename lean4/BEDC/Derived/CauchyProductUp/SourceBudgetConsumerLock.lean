import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_budget_radius_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          PkgSig bundle budgetSeal pkg ->
            UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory observationA ∧
              UnaryHistory observationB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont classifier routes budgetClassifier ∧
                      Cont budgetClassifier ledger budgetSeal ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute budgetSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  exact
    ⟨radiusAUnary, radiusBUnary, observationAUnary, observationBUnary, productUnary,
      classifierUnary, budgetClassifierUnary, budgetSealUnary, productRoute,
      classifierRoute, classifierBudget, budgetSealRoute, namePkg, budgetSealPkg⟩

theorem CauchyProductPacket_source_window_bilinear_synchronization [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name sourceWindowA sourceWindowB
      synchronizedProduct : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont sourceA windowA sourceWindowA ->
        Cont sourceB windowB sourceWindowB ->
          Cont sourceWindowA sourceWindowB synchronizedProduct ->
            PkgSig bundle synchronizedProduct pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory sourceWindowA ∧
                  UnaryHistory sourceWindowB ∧ UnaryHistory synchronizedProduct ∧
                    Cont sourceA windowA sourceWindowA ∧
                      Cont sourceB windowB sourceWindowB ∧
                        Cont sourceWindowA sourceWindowB synchronizedProduct ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle synchronizedProduct pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceWindowRouteA sourceWindowRouteB synchronizedRoute synchronizedPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have sourceWindowAUnary : UnaryHistory sourceWindowA :=
    unary_cont_closed sourceAUnary windowAUnary sourceWindowRouteA
  have sourceWindowBUnary : UnaryHistory sourceWindowB :=
    unary_cont_closed sourceBUnary windowBUnary sourceWindowRouteB
  have synchronizedProductUnary : UnaryHistory synchronizedProduct :=
    unary_cont_closed sourceWindowAUnary sourceWindowBUnary synchronizedRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, sourceWindowAUnary,
      sourceWindowBUnary, synchronizedProductUnary, sourceWindowRouteA, sourceWindowRouteB,
      synchronizedRoute, namePkg, synchronizedPkg⟩

end BEDC.Derived.CauchyProductUp
