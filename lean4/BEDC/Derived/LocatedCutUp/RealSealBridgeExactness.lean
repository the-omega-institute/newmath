import BEDC.Derived.LocatedCutUp

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCutCarrier_real_seal_bridge_exactness [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert bridge
      realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff sealRow bridge ->
                  Cont sealRow provenance realConsumer ->
                    PkgSig bundle bridge pkg ->
                      PkgSig bundle realConsumer pkg ->
                        hsame handoff provenance ∧ UnaryHistory bridge ∧
                          UnaryHistory realConsumer ∧ Cont lower upper window ∧
                            Cont window handoff transportRow ∧ Cont handoff sealRow bridge ∧
                              Cont sealRow provenance realConsumer ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
                                  PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary handoffSealBridge
    sealProvenanceConsumer bridgePkg consumerPkg
  obtain ⟨bridgeUnary, realConsumerUnary, sameHandoffProvenance, lowerUpperWindow,
    windowHandoffTransport, bridgeRoute, consumerRoute, provenancePkg, bridgePackage,
    consumerPackage⟩ :=
    LocatedCutCarrier_scoped_kernel_route carrier lowerUnary upperUnary handoffUnary routeUnary
      localCertUnary handoffSealBridge bridgePkg sealProvenanceConsumer consumerPkg
  exact
    ⟨sameHandoffProvenance, bridgeUnary, realConsumerUnary, lowerUpperWindow,
      windowHandoffTransport, bridgeRoute, consumerRoute, provenancePkg, bridgePackage,
      consumerPackage⟩

end BEDC.Derived.LocatedCutUp
