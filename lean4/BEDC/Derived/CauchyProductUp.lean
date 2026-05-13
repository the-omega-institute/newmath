import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyProductPacket [AskSetup] [PackageSetup]
    (sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
    UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
      UnaryHistory observationA ∧ UnaryHistory observationB ∧ UnaryHistory routes ∧
        UnaryHistory ledger ∧ Cont windowA windowB transport ∧
          Cont observationA observationB product ∧ Cont product ledger classifier ∧
            PkgSig bundle name pkg

theorem CauchyProductPacket_namecert_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
        UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
          UnaryHistory product ∧ UnaryHistory classifier ∧ Cont windowA windowB transport ∧
            Cont observationA observationB product ∧ Cont product ledger classifier ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      productUnary, classifierUnary, windowTransport, productRoute, classifierRoute, namePkg⟩

theorem CauchyProductPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        PkgSig bundle realSeal pkg ->
          UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
            Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
              PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet classifierRoutesRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  exact
    ⟨productUnary, classifierUnary, realSealUnary, classifierRoute, classifierRoutesRealSeal,
      namePkg, realSealPkg⟩

theorem CauchyProductPacket_window_product_stability [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
        UnaryHistory observationB ∧ UnaryHistory product ∧
          Cont observationA observationB product ∧ Cont windowA windowB transport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    windowTransport, productRoute, _classifierRoute, _namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      productRoute, windowTransport⟩

end BEDC.Derived.CauchyProductUp
