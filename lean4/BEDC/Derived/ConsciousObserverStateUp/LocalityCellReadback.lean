import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_locality_cell_readback [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint
      localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        nameRow endpoint bundle pkg →
      Cont state provenance localityRead →
        PkgSig bundle localityRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ConsciousObserverStateCarrier observer state recognition ledger gap transport route
                    provenance nameRow endpoint bundle pkg ∧
                  hsame row localityRead)
              (fun row : BHist => hsame row localityRead ∧ Cont state provenance row)
              (fun _row : BHist => PkgSig bundle localityRead pkg ∧ Cont observer route endpoint)
              hsame ∧
            UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
              UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory provenance ∧
                UnaryHistory localityRead ∧ Cont observer route endpoint ∧
                  Cont state route endpoint ∧ Cont state provenance localityRead ∧
                    Cont recognition ledger gap ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle localityRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier stateProvenanceLocality localityPkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        nameRow endpoint bundle pkg :=
    carrier
  obtain ⟨observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, _routeUnary, provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed stateUnary provenanceUnary stateProvenanceLocality
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
                provenance nameRow endpoint bundle pkg ∧
              hsame row localityRead)
          (fun row : BHist => hsame row localityRead ∧ Cont state provenance row)
          (fun _row : BHist => PkgSig bundle localityRead pkg ∧ Cont observer route endpoint)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro localityRead ⟨carrierPacket, hsame_refl localityRead⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameLocality : hsame row localityRead := source.right
      exact
        ⟨rowSameLocality,
          cont_result_hsame_transport stateProvenanceLocality (hsame_symm rowSameLocality)⟩
    · intro _row _source
      exact ⟨localityPkg, observerRouteEndpoint⟩
  exact
    ⟨cert, observerUnary, stateUnary, recognitionUnary, ledgerUnary, gapUnary,
      provenanceUnary, localityUnary, observerRouteEndpoint, stateRouteEndpoint,
      stateProvenanceLocality, recognitionLedgerGap, endpointPkg, localityPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
