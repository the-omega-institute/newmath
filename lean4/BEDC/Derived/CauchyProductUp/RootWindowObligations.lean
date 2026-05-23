import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_window_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
        UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
          UnaryHistory observationA ∧ UnaryHistory observationB ∧
            Cont windowA windowB transport ∧ Cont observationA observationB product ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, windowTransport, productRoute, namePkg⟩

theorem CauchyProductPacket_budgeted_readback_root_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes budgetRead ->
            PkgSig bundle budgetRead pkg ->
              UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
                UnaryHistory observationB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                    UnaryHistory budgetRead ∧ Cont windowA windowB transport ∧
                      Cont observationA observationB product ∧ Cont product ledger classifier ∧
                        Cont classifier routes budgetClassifier ∧
                          Cont budgetClassifier ledger budgetSeal ∧
                            Cont budgetSeal routes budgetRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute sealBudgetRead budgetReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetSealUnary routesUnary sealBudgetRead
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      classifierUnary, budgetClassifierUnary, budgetSealUnary, budgetReadUnary,
      windowTransport, productRoute, classifierRoute, classifierBudget, budgetSealRoute,
      sealBudgetRead, namePkg, budgetReadPkg⟩

end BEDC.Derived.CauchyProductUp
