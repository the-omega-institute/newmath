import BEDC.Derived.LocatedCutUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCutCarrier_public_namecert_export [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert bridge
      realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg →
      UnaryHistory lower →
        UnaryHistory upper →
          UnaryHistory handoff →
            UnaryHistory route →
              UnaryHistory localCert →
                Cont handoff sealRow bridge →
                  Cont sealRow provenance realConsumer →
                    PkgSig bundle bridge pkg →
                      PkgSig bundle realConsumer pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              LocatedCutCarrier lower upper window handoff sealRow transportRow route
                                  provenance localCert bundle pkg ∧
                                hsame row sealRow)
                            (fun row : BHist =>
                              hsame row handoff ∨ hsame row provenance ∨ hsame row bridge ∨
                                hsame row realConsumer)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
                                PkgSig bundle realConsumer pkg ∧ hsame row sealRow)
                            hsame ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
                            PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary handoffSealBridge
    sealProvenanceConsumer bridgePkg consumerPkg
  obtain ⟨cert, _sameHandoffProvenance, _bridgeUnary, _realConsumerUnary, _lowerUpperWindow,
    _windowHandoffTransport, _bridgeRoute, _consumerRoute⟩ :=
    LocatedCutCarrier_obligation_scope_package carrier lowerUnary upperUnary handoffUnary routeUnary
      localCertUnary handoffSealBridge sealProvenanceConsumer bridgePkg consumerPkg
  obtain ⟨_lowerUpperWindow, _windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, _sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  exact ⟨cert, provenancePkg, bridgePkg, consumerPkg⟩

end BEDC.Derived.LocatedCutUp
