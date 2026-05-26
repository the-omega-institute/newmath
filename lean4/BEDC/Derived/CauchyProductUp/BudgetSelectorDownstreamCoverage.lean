import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_selector_downstream_coverage [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name selectorWindow selectorDyadic selectorRegular
      productSeal budgetClassifier budgetSeal downstreamRead : BHist}
    {bundle selectorBundle : ProbeBundle ProbeName} {pkg selectorPkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont selectorWindow selectorDyadic selectorRegular →
        Cont product selectorRegular productSeal →
          Cont classifier routes budgetClassifier →
            Cont budgetClassifier ledger budgetSeal →
              Cont budgetSeal routes downstreamRead →
                PkgSig selectorBundle selectorRegular selectorPkg →
                  PkgSig bundle downstreamRead pkg →
                    UnaryHistory selectorWindow →
                      UnaryHistory selectorDyadic →
                        UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
                          UnaryHistory selectorRegular ∧ UnaryHistory productSeal ∧
                            UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                              UnaryHistory downstreamRead ∧
                                Cont selectorWindow selectorDyadic selectorRegular ∧
                                  Cont product selectorRegular productSeal ∧
                                    Cont classifier routes budgetClassifier ∧
                                      Cont budgetClassifier ledger budgetSeal ∧
                                        Cont budgetSeal routes downstreamRead ∧
                                          PkgSig bundle name pkg ∧
                                            PkgSig selectorBundle selectorRegular selectorPkg ∧
                                              PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet selectorRoute productSealRoute budgetClassifierRoute budgetSealRoute
    downstreamRoute selectorPkgSig downstreamPkg selectorWindowUnary selectorDyadicUnary
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
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed budgetSealUnary routesUnary downstreamRoute
  exact
    ⟨windowAUnary, windowBUnary, productUnary, selectorRegularUnary, productSealUnary,
      budgetClassifierUnary, budgetSealUnary, downstreamReadUnary, selectorRoute,
      productSealRoute, budgetClassifierRoute, budgetSealRoute, downstreamRoute, namePkg,
      selectorPkgSig, downstreamPkg⟩

end BEDC.Derived.CauchyProductUp
