import BEDC.Derived.CauchyProductUp
import BEDC.Derived.RealObservationBudgetUp.TasteGate

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_seal_upstream_budget_factorization [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetEntry budgetWindow budgetDyadic budgetReadback
      budgetSeal budgetTransport budgetClassifier budgetPkgRow budgetName realSeal
      completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            Cont realSeal ledger completionConsumer ->
              PkgSig bundle completionConsumer pkg ->
                (∃ observed : BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp,
                  observed =
                      BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp.mk
                        budgetEntry budgetWindow budgetDyadic budgetReadback budgetSeal
                        budgetTransport budgetClassifier budgetPkgRow budgetName ∧
                    UnaryHistory product ∧ UnaryHistory classifier ∧
                      UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                        UnaryHistory realSeal ∧ UnaryHistory completionConsumer ∧
                          Cont product ledger classifier ∧
                            Cont classifier routes budgetClassifier ∧
                              Cont budgetClassifier ledger budgetSeal ∧
                                Cont budgetSeal routes realSeal ∧
                                  Cont realSeal ledger completionConsumer ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle completionConsumer pkg) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute completionConsumerRoute
    completionConsumerPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary routesUnary realSealRoute
  have completionConsumerUnary : UnaryHistory completionConsumer :=
    unary_cont_closed realSealUnary ledgerUnary completionConsumerRoute
  exact
    ⟨BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp.mk budgetEntry budgetWindow
        budgetDyadic budgetReadback budgetSeal budgetTransport budgetClassifier budgetPkgRow
        budgetName,
      rfl, productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary, realSealUnary,
      completionConsumerUnary, classifierRoute, classifierBudget, budgetSealRoute, realSealRoute,
      completionConsumerRoute, namePkg, completionConsumerPkg⟩

end BEDC.Derived.CauchyProductUp
