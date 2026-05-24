import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_seal_root_surface [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal budgetClassifier budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        PkgSig bundle realSeal pkg ->
          Cont classifier routes budgetClassifier ->
            Cont budgetClassifier ledger budgetSeal ->
              PkgSig bundle budgetSeal pkg ->
                UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                  UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                    Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
                      Cont classifier routes budgetClassifier ∧
                        Cont budgetClassifier ledger budgetSeal ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle realSeal pkg ∧ PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet classifierRealSeal realSealPkg classifierBudget budgetSealRoute budgetSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRealSeal
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  exact
    ⟨productUnary, classifierUnary, realSealUnary, budgetClassifierUnary, budgetSealUnary,
      classifierRoute, classifierRealSeal, classifierBudget, budgetSealRoute, namePkg,
      realSealPkg, budgetSealPkg⟩

end BEDC.Derived.CauchyProductUp
