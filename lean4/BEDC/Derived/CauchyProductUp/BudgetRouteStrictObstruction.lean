import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_route_strict_obstruction [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal
      obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            Cont realSeal ledger obstructionRead ->
              PkgSig bundle obstructionRead pkg ->
                UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                  UnaryHistory realSeal ∧ UnaryHistory obstructionRead ∧
                    Cont classifier routes budgetClassifier ∧
                      Cont budgetClassifier ledger budgetSeal ∧
                        Cont budgetSeal routes realSeal ∧
                          Cont realSeal ledger obstructionRead ∧
                            PkgSig bundle name pkg ∧
                              PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute budgetSealRealSeal realSealObstruction
    obstructionPkg
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
    unary_cont_closed budgetSealUnary routesUnary budgetSealRealSeal
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed realSealUnary ledgerUnary realSealObstruction
  exact
    ⟨budgetClassifierUnary, budgetSealUnary, realSealUnary, obstructionUnary,
      classifierBudget, budgetSealRoute, budgetSealRealSeal, realSealObstruction, namePkg,
      obstructionPkg⟩

end BEDC.Derived.CauchyProductUp
