import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_seal_selector_coherence [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal
      siblingSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            Cont budgetSeal ledger siblingSeal ->
              PkgSig bundle realSeal pkg ->
                PkgSig bundle siblingSeal pkg ->
                  UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory realSeal ∧ UnaryHistory siblingSeal ∧
                        Cont observationA observationB product ∧
                          Cont product ledger classifier ∧
                            Cont classifier routes budgetClassifier ∧
                              Cont budgetClassifier ledger budgetSeal ∧
                                Cont budgetSeal routes realSeal ∧
                                  Cont budgetSeal ledger siblingSeal ∧
                                    PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg ∧
                                      PkgSig bundle siblingSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet classifierBudget budgetSealRoute realSealRoute siblingSealRoute realSealPkg
    siblingSealPkg
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
  have siblingSealUnary : UnaryHistory siblingSeal :=
    unary_cont_closed budgetSealUnary ledgerUnary siblingSealRoute
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary, realSealUnary,
      siblingSealUnary, productRoute, classifierRoute, classifierBudget, budgetSealRoute,
      realSealRoute, siblingSealRoute, namePkg, realSealPkg, siblingSealPkg⟩

end BEDC.Derived.CauchyProductUp
