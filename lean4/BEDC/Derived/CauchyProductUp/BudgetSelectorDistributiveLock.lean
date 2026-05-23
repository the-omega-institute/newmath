import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_selector_distributive_lock [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name selectorWindow selectorDyadic selectorRegular
      productSeal : BHist}
    {bundle selectorBundle : ProbeBundle ProbeName} {pkg selectorPkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont selectorWindow selectorDyadic selectorRegular ->
        Cont product selectorRegular productSeal ->
          PkgSig selectorBundle selectorRegular selectorPkg ->
            UnaryHistory selectorWindow ->
              UnaryHistory selectorDyadic ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
                  UnaryHistory selectorRegular ∧ UnaryHistory productSeal ∧
                    Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                      Cont selectorWindow selectorDyadic selectorRegular ∧
                        Cont product selectorRegular productSeal ∧ PkgSig bundle name pkg ∧
                          PkgSig selectorBundle selectorRegular selectorPkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet selectorRegularRoute productSealRoute selectorRegularPkg selectorWindowUnary
    selectorDyadicUnary
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have selectorRegularUnary : UnaryHistory selectorRegular :=
    unary_cont_closed selectorWindowUnary selectorDyadicUnary selectorRegularRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed productUnary selectorRegularUnary productSealRoute
  exact
    ⟨windowAUnary, windowBUnary, productUnary, selectorRegularUnary, productSealUnary,
      windowTransport, productRoute, selectorRegularRoute, productSealRoute, namePkg,
      selectorRegularPkg⟩

theorem CauchyProductPacket_regseqrat_product_seal_coverage [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal regseqSeal
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes regseqSeal ->
        Cont classifier routes budgetClassifier ->
          Cont budgetClassifier ledger budgetSeal ->
            Cont budgetSeal routes consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
                  UnaryHistory observationB ∧ UnaryHistory product ∧
                    UnaryHistory classifier ∧ UnaryHistory regseqSeal ∧
                      UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                        UnaryHistory consumerRead ∧ Cont observationA observationB product ∧
                          Cont product ledger classifier ∧ Cont classifier routes regseqSeal ∧
                            Cont classifier routes budgetClassifier ∧
                              Cont budgetClassifier ledger budgetSeal ∧
                                Cont budgetSeal routes consumerRead ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet regseqRoute budgetClassifierRoute budgetSealRoute consumerRoute consumerPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary regseqRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary budgetClassifierRoute
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed budgetSealUnary routesUnary consumerRoute
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      classifierUnary, regseqUnary, budgetClassifierUnary, budgetSealUnary, consumerUnary,
      productRoute, classifierRoute, regseqRoute, budgetClassifierRoute, budgetSealRoute,
      consumerRoute, namePkg, consumerPkg⟩

end BEDC.Derived.CauchyProductUp
