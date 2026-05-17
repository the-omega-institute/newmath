import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_gap_consumer_exactness [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint consumer
      publicRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        nameRow endpoint bundle pkg →
      hsame consumer gap →
        Cont route provenance publicRoute →
          PkgSig bundle publicRoute pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ConsciousObserverStateCarrier observer state recognition ledger gap transport
                    route provenance nameRow endpoint bundle pkg ∧ hsame row gap)
                (fun row : BHist =>
                  hsame row gap ∧ UnaryHistory row ∧ Cont recognition ledger gap)
                (fun row : BHist =>
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRoute pkg ∧
                    hsame row gap ∧ Cont route provenance publicRoute)
                hsame ∧
              UnaryHistory consumer ∧ UnaryHistory state ∧ UnaryHistory ledger ∧
                UnaryHistory gap ∧ UnaryHistory publicRoute ∧ Cont recognition ledger gap ∧
                  Cont route provenance publicRoute ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle publicRoute pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier consumerSame routeProvenancePublic publicPkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg :=
    carrier
  obtain ⟨_observerUnary, stateUnary, _recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, routeUnary, provenanceUnary, _nameUnary, _endpointUnary,
    _observerRouteEndpoint, _stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_transport gapUnary (hsame_symm consumerSame)
  have publicUnary : UnaryHistory publicRoute :=
    unary_cont_closed routeUnary provenanceUnary routeProvenancePublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance nameRow endpoint bundle pkg ∧ hsame row gap)
          (fun row : BHist =>
            hsame row gap ∧ UnaryHistory row ∧ Cont recognition ledger gap)
          (fun row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRoute pkg ∧ hsame row gap ∧
              Cont route provenance publicRoute)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gap ⟨carrierPacket, hsame_refl gap⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameGap : hsame row gap := source.right
      exact ⟨rowSameGap, unary_transport gapUnary (hsame_symm rowSameGap), recognitionLedgerGap⟩
    · intro row source
      exact ⟨endpointPkg, publicPkg, source.right, routeProvenancePublic⟩
  exact
    ⟨cert, consumerUnary, stateUnary, ledgerUnary, gapUnary, publicUnary,
      recognitionLedgerGap, routeProvenancePublic, endpointPkg, publicPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
