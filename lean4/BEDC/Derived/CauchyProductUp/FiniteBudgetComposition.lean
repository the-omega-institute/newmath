import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_finite_budget_composition [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetRead realBudgetSeal seriesConsumer
      finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont windowA routes budgetRead ->
        Cont budgetRead ledger realBudgetSeal ->
          Cont realBudgetSeal routes seriesConsumer ->
            Cont seriesConsumer ledger finalRead ->
              PkgSig bundle finalRead pkg ->
                UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                  UnaryHistory windowB ∧ UnaryHistory budgetRead ∧
                    UnaryHistory realBudgetSeal ∧ UnaryHistory seriesConsumer ∧
                      UnaryHistory finalRead ∧ Cont windowA routes budgetRead ∧
                        Cont budgetRead ledger realBudgetSeal ∧
                          Cont realBudgetSeal routes seriesConsumer ∧
                            Cont seriesConsumer ledger finalRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet windowBudget budgetRealSeal realSealConsumer consumerFinal finalPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowAUnary routesUnary windowBudget
  have realBudgetSealUnary : UnaryHistory realBudgetSeal :=
    unary_cont_closed budgetReadUnary ledgerUnary budgetRealSeal
  have seriesConsumerUnary : UnaryHistory seriesConsumer :=
    unary_cont_closed realBudgetSealUnary routesUnary realSealConsumer
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed seriesConsumerUnary ledgerUnary consumerFinal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, budgetReadUnary,
      realBudgetSealUnary, seriesConsumerUnary, finalReadUnary, windowBudget,
      budgetRealSeal, realSealConsumer, consumerFinal, namePkg, finalPkg⟩

end BEDC.Derived.CauchyProductUp
