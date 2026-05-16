import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_locality_cell_handoff [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint
      localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        nameRow endpoint bundle pkg →
      Cont endpoint provenance localityRead →
        PkgSig bundle localityRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ConsciousObserverStateCarrier observer state recognition ledger gap transport route
                  provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle endpoint pkg ∧ hsame row endpoint ∧
                  Cont endpoint provenance localityRead)
              hsame ∧
            UnaryHistory observer ∧
            UnaryHistory state ∧
            UnaryHistory localityRead ∧
            Cont observer route endpoint ∧
            Cont state route endpoint ∧
            Cont endpoint provenance localityRead ∧
            PkgSig bundle endpoint pkg ∧
            PkgSig bundle localityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier endpointProvenanceLocality localityPkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg :=
    carrier
  obtain ⟨observerUnary, stateUnary, _recognitionUnary, _ledgerUnary, _gapUnary,
    _transportUnary, _routeUnary, provenanceUnary, _nameUnary, endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, _recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed endpointUnary provenanceUnary endpointProvenanceLocality
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle endpoint pkg ∧ hsame row endpoint ∧
              Cont endpoint provenance localityRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro endpoint ⟨carrierPacket, hsame_refl endpoint⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameEndpoint : hsame row endpoint := source.right
      exact
        ⟨rowSameEndpoint,
          unary_transport endpointUnary (hsame_symm rowSameEndpoint)⟩
    · intro row source
      exact ⟨endpointPkg, source.right, endpointProvenanceLocality⟩
  exact
    ⟨cert, observerUnary, stateUnary, localityUnary, observerRouteEndpoint,
      stateRouteEndpoint, endpointProvenanceLocality, endpointPkg, localityPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
