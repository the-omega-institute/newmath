import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_real_seal_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name rootSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes rootSeal →
        PkgSig bundle rootSeal pkg →
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory rootSeal ∧
                Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                  Cont product ledger classifier ∧ Cont classifier routes rootSeal ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle rootSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRootSeal rootSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRootSeal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      productUnary, classifierUnary, rootSealUnary, windowTransport, productRoute,
      classifierRoute, classifierRootSeal, namePkg, rootSealPkg⟩

theorem CauchyProductPacket_root_real_seal_factorization [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        PkgSig bundle realSeal pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
              UnaryHistory observationA ∧ UnaryHistory observationB ∧ UnaryHistory product ∧
                UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                  Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                    Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRoutesRealSeal realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary, realSealUnary,
      windowTransport, productRoute, classifierRoute, classifierRoutesRealSeal, namePkg,
      realSealPkg⟩

end BEDC.Derived.CauchyProductUp
