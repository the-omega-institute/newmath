import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_regular_product_downstream_coverage [AskSetup]
    [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            Cont realSeal ledger downstream ->
              PkgSig bundle downstream pkg ->
                UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                  UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
                    UnaryHistory observationA ∧ UnaryHistory observationB ∧
                      UnaryHistory product ∧ UnaryHistory classifier ∧
                        UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                          UnaryHistory realSeal ∧ UnaryHistory downstream ∧
                            Cont observationA observationB product ∧
                              Cont product ledger classifier ∧
                                Cont classifier routes budgetClassifier ∧
                                  Cont budgetClassifier ledger budgetSeal ∧
                                    Cont budgetSeal routes realSeal ∧
                                      Cont realSeal ledger downstream ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute downstreamRoute downstreamPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
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
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary routesUnary realSealRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed realSealUnary ledgerUnary downstreamRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
      radiusBUnary, observationAUnary, observationBUnary, productUnary, classifierUnary,
      budgetClassifierUnary, budgetSealUnary, realSealUnary, downstreamUnary,
      productRoute, classifierRoute, classifierBudget, budgetSealRoute, realSealRoute,
      downstreamRoute, namePkg, downstreamPkg⟩

end BEDC.Derived.CauchyProductUp
