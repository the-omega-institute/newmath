import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_factor_source_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes budgetClassifier →
        UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
          UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
            UnaryHistory observationA ∧ UnaryHistory observationB ∧ UnaryHistory product ∧
              UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                Cont observationA observationB product ∧ Cont product ledger classifier ∧
                  Cont classifier routes budgetClassifier ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet classifierRoutesBudget
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesBudget
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary,
      budgetClassifierUnary, productRoute, classifierRoute, classifierRoutesBudget, namePkg⟩

end BEDC.Derived.CauchyProductUp
