import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_componentwise_window_admission [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name leftWindowRead rightWindowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont windowA routes leftWindowRead ->
        Cont windowB routes rightWindowRead ->
          PkgSig bundle leftWindowRead pkg ->
            PkgSig bundle rightWindowRead pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory leftWindowRead ∧
                  UnaryHistory rightWindowRead ∧ Cont windowA windowB transport ∧
                    Cont windowA routes leftWindowRead ∧
                      Cont windowB routes rightWindowRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle leftWindowRead pkg ∧
                          PkgSig bundle rightWindowRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet windowALeftRead windowBRightRead leftReadPkg rightReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, routesUnary, _ledgerUnary,
    windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have leftReadUnary : UnaryHistory leftWindowRead :=
    unary_cont_closed windowAUnary routesUnary windowALeftRead
  have rightReadUnary : UnaryHistory rightWindowRead :=
    unary_cont_closed windowBUnary routesUnary windowBRightRead
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, leftReadUnary,
      rightReadUnary, windowTransport, windowALeftRead, windowBRightRead, namePkg,
      leftReadPkg, rightReadPkg⟩

theorem CauchyProductPacket_public_budget_route_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name finiteApproxRead observationBudgetRead
      limitSealRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes finiteApproxRead ->
        Cont finiteApproxRead ledger observationBudgetRead ->
          Cont observationBudgetRead routes limitSealRead ->
            Cont limitSealRead ledger finalRead ->
              PkgSig bundle finalRead pkg ->
                UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory finiteApproxRead ∧ UnaryHistory observationBudgetRead ∧
                    UnaryHistory limitSealRead ∧ UnaryHistory finalRead ∧
                      Cont observationA observationB product ∧
                        Cont product ledger classifier ∧
                          Cont classifier routes finiteApproxRead ∧
                            Cont finiteApproxRead ledger observationBudgetRead ∧
                              Cont observationBudgetRead routes limitSealRead ∧
                                Cont limitSealRead ledger finalRead ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet classifierFinite finiteObservation observationLimit limitFinal finalPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have finiteApproxUnary : UnaryHistory finiteApproxRead :=
    unary_cont_closed classifierUnary routesUnary classifierFinite
  have observationBudgetUnary : UnaryHistory observationBudgetRead :=
    unary_cont_closed finiteApproxUnary ledgerUnary finiteObservation
  have limitSealUnary : UnaryHistory limitSealRead :=
    unary_cont_closed observationBudgetUnary routesUnary observationLimit
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed limitSealUnary ledgerUnary limitFinal
  exact
    ⟨productUnary, classifierUnary, finiteApproxUnary, observationBudgetUnary,
      limitSealUnary, finalReadUnary, productRoute, classifierRoute, classifierFinite,
      finiteObservation, observationLimit, limitFinal, namePkg, finalPkg⟩

theorem CauchyProductPacket_real_handoff_nonescape [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name finiteApproxRead observationBudgetRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes finiteApproxRead ->
        Cont finiteApproxRead ledger observationBudgetRead ->
          Cont observationBudgetRead routes realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory finiteApproxRead ∧ UnaryHistory observationBudgetRead ∧
                  UnaryHistory realSeal ∧ Cont observationA observationB product ∧
                    Cont product ledger classifier ∧
                      Cont classifier routes finiteApproxRead ∧
                        Cont finiteApproxRead ledger observationBudgetRead ∧
                          Cont observationBudgetRead routes realSeal ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet classifierFinite finiteObservation observationReal realPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have finiteApproxUnary : UnaryHistory finiteApproxRead :=
    unary_cont_closed classifierUnary routesUnary classifierFinite
  have observationBudgetUnary : UnaryHistory observationBudgetRead :=
    unary_cont_closed finiteApproxUnary ledgerUnary finiteObservation
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed observationBudgetUnary routesUnary observationReal
  exact
    ⟨productUnary, classifierUnary, finiteApproxUnary, observationBudgetUnary,
      realSealUnary, productRoute, classifierRoute, classifierFinite, finiteObservation,
      observationReal, namePkg, realPkg⟩

end BEDC.Derived.CauchyProductUp
