import BEDC.Derived.LocatedCutUp

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCutCarrier_bridge_boundary_package [AskSetup] [PackageSetup]
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
                        SemanticNameCert
                            (fun row : BHist =>
                              LocatedCutCarrier lower upper window handoff sealRow transportRow route
                                  provenance localCert bundle pkg ∧
                                hsame row sealRow)
                            (fun row : BHist =>
                              hsame row handoff ∨ hsame row bridge ∨ hsame row realConsumer ∨
                                hsame row provenance)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
                                PkgSig bundle realConsumer pkg ∧ hsame row sealRow)
                            hsame ∧
                          hsame handoff provenance ∧ UnaryHistory bridge ∧
                            UnaryHistory realConsumer ∧ Cont lower upper window ∧
                              Cont window handoff transportRow ∧
                                Cont handoff sealRow bridge ∧
                                  Cont sealRow provenance realConsumer ∧
                                    PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
                                      PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary handoffSealBridge
    sealProvenanceConsumer bridgePkg consumerPkg
  have carrierPacket :
      LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg :=
    carrier
  obtain ⟨_scopedCert, sameHandoffProvenance, bridgeUnary, realConsumerUnary,
    lowerUpperWindow, windowHandoffTransport, bridgeRoute, consumerRoute⟩ :=
    LocatedCutCarrier_obligation_scope_package carrier lowerUnary upperUnary handoffUnary
      routeUnary localCertUnary handoffSealBridge sealProvenanceConsumer bridgePkg consumerPkg
  obtain ⟨_lowerUpperWindow, _windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have sourceSeal :
      (fun row : BHist =>
        LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧
          hsame row sealRow) sealRow := by
    exact ⟨carrierPacket, hsame_refl sealRow⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance
                localCert bundle pkg ∧
              hsame row sealRow)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row bridge ∨ hsame row realConsumer ∨
              hsame row provenance)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
              PkgSig bundle realConsumer pkg ∧ hsame row sealRow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact Or.inl (hsame_trans source.right sameSealHandoff)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, bridgePkg, consumerPkg, source.right⟩
  }
  exact
    ⟨cert, sameHandoffProvenance, bridgeUnary, realConsumerUnary, lowerUpperWindow,
      windowHandoffTransport, bridgeRoute, consumerRoute, provenancePkg, bridgePkg,
      consumerPkg⟩

end BEDC.Derived.LocatedCutUp
