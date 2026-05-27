import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_public_multiplication_consumer_boundary [AskSetup]
    [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal publicConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        Cont realSeal ledger publicConsumer ->
          PkgSig bundle publicConsumer pkg ->
            UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory radiusA ∧
              UnaryHistory radiusB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory realSeal ∧ UnaryHistory publicConsumer ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont classifier routes realSeal ∧ Cont realSeal ledger publicConsumer ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle publicConsumer pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet classifierRealSeal realSealConsumer consumerPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRealSeal
  have publicConsumerUnary : UnaryHistory publicConsumer :=
    unary_cont_closed realSealUnary ledgerUnary realSealConsumer
  exact
    ⟨windowAUnary, windowBUnary, radiusAUnary, radiusBUnary, productUnary,
      classifierUnary, realSealUnary, publicConsumerUnary, productRoute, classifierRoute,
      classifierRealSeal, realSealConsumer, namePkg, consumerPkg⟩

end BEDC.Derived.CauchyProductUp
