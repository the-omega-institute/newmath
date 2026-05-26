import BEDC.Derived.CauchyProductUp
import BEDC.Derived.RealObservationBudgetUp.TasteGate

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_route_exactness [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name finiteApprox budgetRead exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes finiteApprox ->
        Cont finiteApprox ledger budgetRead ->
          Cont budgetRead routes exactRead ->
            PkgSig bundle exactRead pkg ->
              UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory product ∧
                UnaryHistory classifier ∧ UnaryHistory finiteApprox ∧
                  UnaryHistory budgetRead ∧ UnaryHistory exactRead ∧
                    Cont observationA observationB product ∧ Cont product ledger classifier ∧
                      Cont classifier routes finiteApprox ∧
                        Cont finiteApprox ledger budgetRead ∧
                          Cont budgetRead routes exactRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle exactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierFinite finiteBudget budgetExact exactPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have finiteApproxUnary : UnaryHistory finiteApprox :=
    unary_cont_closed classifierUnary routesUnary classifierFinite
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed finiteApproxUnary ledgerUnary finiteBudget
  have exactReadUnary : UnaryHistory exactRead :=
    unary_cont_closed budgetReadUnary routesUnary budgetExact
  exact
    ⟨radiusAUnary, radiusBUnary, productUnary, classifierUnary, finiteApproxUnary,
      budgetReadUnary, exactReadUnary, productRoute, classifierRoute, classifierFinite,
      finiteBudget, budgetExact, namePkg, exactPkg⟩

theorem CauchyProductPacket_dyadic_radius_ledger_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetEntry budgetWindow budgetDyadic
      budgetReadback budgetSeal budgetTransport budgetClassifier budgetPkgRow
      budgetName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          PkgSig bundle budgetSeal pkg ->
            (∃ observed : BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp,
              observed =
                  BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp.mk
                    budgetEntry budgetWindow budgetDyadic budgetReadback budgetSeal
                    budgetTransport budgetClassifier budgetPkgRow budgetName ∧
                UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory product ∧
                  UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                    UnaryHistory budgetSeal ∧ Cont observationA observationB product ∧
                      Cont product ledger classifier ∧
                        Cont classifier routes budgetClassifier ∧
                          Cont budgetClassifier ledger budgetSeal ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle budgetSeal pkg) := by
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
    ⟨BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp.mk budgetEntry
        budgetWindow budgetDyadic budgetReadback budgetSeal budgetTransport budgetClassifier
        budgetPkgRow budgetName,
      rfl, radiusAUnary, radiusBUnary, productUnary, classifierUnary, budgetClassifierUnary,
      budgetSealUnary, productRoute, classifierRoute, classifierBudget, budgetSealRoute,
      namePkg, budgetSealPkg⟩

end BEDC.Derived.CauchyProductUp
