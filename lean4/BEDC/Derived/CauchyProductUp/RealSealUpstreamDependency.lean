import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_seal_upstream_dependency [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        Cont realSeal ledger completionConsumer ->
          PkgSig bundle completionConsumer pkg ->
            UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
              UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                UnaryHistory completionConsumer ∧ Cont observationA observationB product ∧
                  Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
                    Cont realSeal ledger completionConsumer ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle completionConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet classifierRoutesRealSeal realSealLedgerConsumer completionConsumerPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  have completionConsumerUnary : UnaryHistory completionConsumer :=
    unary_cont_closed realSealUnary ledgerUnary realSealLedgerConsumer
  exact
    ⟨windowAUnary, windowBUnary, productUnary, classifierUnary, realSealUnary,
      completionConsumerUnary, productRoute, classifierRoute, classifierRoutesRealSeal,
      realSealLedgerConsumer, namePkg, completionConsumerPkg⟩

end BEDC.Derived.CauchyProductUp
