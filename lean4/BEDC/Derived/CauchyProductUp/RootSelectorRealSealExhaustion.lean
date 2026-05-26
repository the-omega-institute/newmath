import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_selector_real_seal_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name selectorWindow selectorDyadic selectorRegular
      productSeal budgetClassifier budgetSeal realSeal : BHist}
    {bundle selectorBundle : ProbeBundle ProbeName} {pkg selectorPkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont selectorWindow selectorDyadic selectorRegular ->
        Cont product selectorRegular productSeal ->
          Cont classifier routes budgetClassifier ->
            Cont budgetClassifier ledger budgetSeal ->
              Cont budgetSeal routes realSeal ->
                PkgSig selectorBundle selectorRegular selectorPkg ->
                  PkgSig bundle realSeal pkg ->
                    UnaryHistory selectorWindow ->
                      UnaryHistory selectorDyadic ->
                        UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
                          UnaryHistory selectorRegular ∧ UnaryHistory productSeal ∧
                            UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                              UnaryHistory realSeal ∧ Cont observationA observationB product ∧
                                Cont selectorWindow selectorDyadic selectorRegular ∧
                                  Cont product selectorRegular productSeal ∧
                                    Cont classifier routes budgetClassifier ∧
                                      Cont budgetClassifier ledger budgetSeal ∧
                                        Cont budgetSeal routes realSeal ∧
                                          PkgSig bundle name pkg ∧
                                            PkgSig selectorBundle selectorRegular selectorPkg ∧
                                              PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet selectorRoute productSealRoute budgetClassifierRoute budgetSealRoute
    realSealRoute selectorPkgSig realSealPkg selectorWindowUnary selectorDyadicUnary
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have selectorRegularUnary : UnaryHistory selectorRegular :=
    unary_cont_closed selectorWindowUnary selectorDyadicUnary selectorRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed productUnary selectorRegularUnary productSealRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary budgetClassifierRoute
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary routesUnary realSealRoute
  exact
    ⟨windowAUnary, windowBUnary, productUnary, selectorRegularUnary, productSealUnary,
      budgetClassifierUnary, budgetSealUnary, realSealUnary, productRoute, selectorRoute,
      productSealRoute, budgetClassifierRoute, budgetSealRoute, realSealRoute, namePkg,
      selectorPkgSig, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
