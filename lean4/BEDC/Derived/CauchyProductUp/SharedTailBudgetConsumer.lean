import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_tail_budget_consumer [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal tailThreshold
      tailSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory tailThreshold ->
        Cont classifier routes budgetClassifier ->
          Cont budgetClassifier ledger budgetSeal ->
            Cont ledger tailThreshold tailSeal ->
              PkgSig bundle budgetSeal pkg ->
                PkgSig bundle tailSeal pkg ->
                  UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory tailSeal ∧ Cont observationA observationB product ∧
                        Cont product ledger classifier ∧
                          Cont classifier routes budgetClassifier ∧
                            Cont budgetClassifier ledger budgetSeal ∧
                              Cont ledger tailThreshold tailSeal ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle budgetSeal pkg ∧ PkgSig bundle tailSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet tailThresholdUnary classifierBudget budgetSealRoute tailSealRoute budgetSealPkg
    tailSealPkg
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
  have tailSealUnary : UnaryHistory tailSeal :=
    unary_cont_closed ledgerUnary tailThresholdUnary tailSealRoute
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary, tailSealUnary,
      productRoute, classifierRoute, classifierBudget, budgetSealRoute, tailSealRoute,
      namePkg, budgetSealPkg, tailSealPkg⟩

end BEDC.Derived.CauchyProductUp
