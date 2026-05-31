import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_main_surface_public_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realBudget realSeries : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realBudget ->
        Cont realBudget ledger realSeries ->
          PkgSig bundle realSeries pkg ->
            UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
              UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory realBudget ∧ UnaryHistory realSeries ∧
                  Cont observationA observationB product ∧
                    Cont product ledger classifier ∧ Cont classifier routes realBudget ∧
                      Cont realBudget ledger realSeries ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle realSeries pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSeries realSeriesPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realBudgetUnary : UnaryHistory realBudget :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have realSeriesUnary : UnaryHistory realSeries :=
    unary_cont_closed realBudgetUnary ledgerUnary budgetSeries
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary,
      classifierUnary, realBudgetUnary, realSeriesUnary, productRoute, classifierRoute,
      classifierBudget, budgetSeries, namePkg, realSeriesPkg⟩

end BEDC.Derived.CauchyProductUp
