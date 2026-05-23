import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_l10_dependency_lattice_aux [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamRead regseqSeal budgetClassifier budgetSeal
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        Cont classifier routes regseqSeal ->
          Cont classifier routes budgetClassifier ->
            Cont budgetClassifier ledger budgetSeal ->
              Cont budgetSeal routes realSeal ->
                UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                  UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
                    UnaryHistory observationA ∧ UnaryHistory observationB ∧
                      UnaryHistory transport ∧ UnaryHistory streamRead ∧
                        UnaryHistory product ∧ UnaryHistory classifier ∧
                          UnaryHistory regseqSeal ∧ UnaryHistory budgetClassifier ∧
                            UnaryHistory budgetSeal ∧ UnaryHistory realSeal ∧
                              Cont windowA windowB transport ∧
                                Cont transport routes streamRead ∧
                                  Cont observationA observationB product ∧
                                    Cont product ledger classifier ∧
                                      Cont classifier routes regseqSeal ∧
                                        Cont classifier routes budgetClassifier ∧
                                          Cont budgetClassifier ledger budgetSeal ∧
                                            Cont budgetSeal routes realSeal ∧
                                              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesStreamRead classifierRoutesRegseq classifierRoutesBudget
    budgetLedgerSeal budgetRoutesReal
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed transportUnary routesUnary transportRoutesStreamRead
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRegseq
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetLedgerSeal
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary routesUnary budgetRoutesReal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, transportUnary, streamReadUnary, productUnary,
      classifierUnary, regseqUnary, budgetClassifierUnary, budgetSealUnary, realSealUnary,
      windowTransport, transportRoutesStreamRead, productRoute, classifierRoute,
      classifierRoutesRegseq, classifierRoutesBudget, budgetLedgerSeal, budgetRoutesReal,
      namePkg⟩

theorem CauchyProductPacket_l10_dependency_lattice [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamRead regseqSeal budgetClassifier budgetSeal
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        Cont classifier routes regseqSeal ->
          Cont classifier routes budgetClassifier ->
            Cont budgetClassifier ledger budgetSeal ->
              Cont budgetSeal routes realSeal ->
                PkgSig bundle streamRead pkg ->
                  PkgSig bundle regseqSeal pkg ->
                    PkgSig bundle budgetSeal pkg ->
                      PkgSig bundle realSeal pkg ->
                        UnaryHistory sourceA ∧ UnaryHistory sourceB ∧
                          UnaryHistory windowA ∧ UnaryHistory windowB ∧
                            UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
                              UnaryHistory observationA ∧ UnaryHistory observationB ∧
                                UnaryHistory transport ∧ UnaryHistory streamRead ∧
                                  UnaryHistory product ∧ UnaryHistory classifier ∧
                                    UnaryHistory regseqSeal ∧
                                      UnaryHistory budgetClassifier ∧
                                        UnaryHistory budgetSeal ∧ UnaryHistory realSeal ∧
                                          Cont windowA windowB transport ∧
                                            Cont transport routes streamRead ∧
                                              Cont observationA observationB product ∧
                                                Cont product ledger classifier ∧
                                                  Cont classifier routes regseqSeal ∧
                                                    Cont classifier routes budgetClassifier ∧
                                                      Cont budgetClassifier ledger budgetSeal ∧
                                                        Cont budgetSeal routes realSeal ∧
                                                          PkgSig bundle name pkg ∧
                                                            PkgSig bundle streamRead pkg ∧
                                                              PkgSig bundle regseqSeal pkg ∧
                                                                PkgSig bundle budgetSeal pkg ∧
                                                                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesStreamRead classifierRoutesRegseq classifierRoutesBudget
    budgetLedgerSeal budgetRoutesReal streamReadPkg regseqPkg budgetPkg realPkg
  have inventory :=
    CauchyProductPacket_l10_dependency_lattice_aux
      (sourceA := sourceA) (sourceB := sourceB) (windowA := windowA)
      (windowB := windowB) (radiusA := radiusA) (radiusB := radiusB)
      (observationA := observationA) (observationB := observationB)
      (product := product) (classifier := classifier) (transport := transport)
      (routes := routes) (ledger := ledger) (name := name) (streamRead := streamRead)
      (regseqSeal := regseqSeal) (budgetClassifier := budgetClassifier)
      (budgetSeal := budgetSeal) (realSeal := realSeal) (bundle := bundle) (pkg := pkg)
      packet transportRoutesStreamRead classifierRoutesRegseq classifierRoutesBudget
      budgetLedgerSeal budgetRoutesReal
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, transportUnary, streamReadUnary,
    productUnary, classifierUnary, regseqUnary, budgetClassifierUnary, budgetSealUnary,
    realSealUnary, windowTransport, streamRoute, productRoute, classifierRoute, regseqRoute,
    budgetRoute, budgetSealRoute, realSealRoute, namePkg⟩ := inventory
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, transportUnary, streamReadUnary, productUnary,
      classifierUnary, regseqUnary, budgetClassifierUnary, budgetSealUnary, realSealUnary,
      windowTransport, streamRoute, productRoute, classifierRoute, regseqRoute, budgetRoute,
      budgetSealRoute, realSealRoute, namePkg, streamReadPkg, regseqPkg, budgetPkg, realPkg⟩

end BEDC.Derived.CauchyProductUp
