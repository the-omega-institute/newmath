import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_budget_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes budgetClassifier →
        Cont budgetClassifier ledger budgetSeal →
          PkgSig bundle budgetSeal pkg →
            UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory observationA ∧
              UnaryHistory observationB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory ledger ∧ UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
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
      classifierUnary, ledgerUnary, budgetClassifierUnary, budgetSealUnary, productRoute,
      classifierRoute, classifierBudget, budgetSealRoute, namePkg, budgetSealPkg⟩

end BEDC.Derived.CauchyProductUp
