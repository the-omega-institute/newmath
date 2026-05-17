import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_current_ledger_handoff [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint
      ledgerConsumer gapConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg →
      hsame ledgerConsumer ledger →
        hsame gapConsumer gap →
          SemanticNameCert
              (fun row : BHist => (hsame row ledger ∨ hsame row gap) ∧ UnaryHistory row)
              (fun row : BHist => (hsame row ledger ∨ hsame row gap) ∧
                Cont recognition ledger gap)
              (fun _row : BHist => PkgSig bundle endpoint pkg ∧
                Cont observer route endpoint ∧ Cont state route endpoint)
              hsame ∧
            UnaryHistory ledgerConsumer ∧ UnaryHistory gapConsumer ∧
              Cont observer route endpoint ∧ Cont state route endpoint ∧
                Cont recognition ledger gap ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerConsumerSame gapConsumerSame
  obtain ⟨_observerUnary, _stateUnary, _recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have ledgerConsumerUnary : UnaryHistory ledgerConsumer :=
    unary_transport_symm ledgerUnary ledgerConsumerSame
  have gapConsumerUnary : UnaryHistory gapConsumer :=
    unary_transport_symm gapUnary gapConsumerSame
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row ledger ∨ hsame row gap) ∧ UnaryHistory row)
          (fun row : BHist => (hsame row ledger ∨ hsame row gap) ∧
            Cont recognition ledger gap)
          (fun _row : BHist => PkgSig bundle endpoint pkg ∧
            Cont observer route endpoint ∧ Cont state route endpoint)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger
          ⟨Or.inl (hsame_refl ledger), ledgerUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        cases source.left with
        | inl rowLedger =>
            exact ⟨Or.inl (hsame_trans (hsame_symm same) rowLedger),
              unary_transport source.right same⟩
        | inr rowGap =>
            exact ⟨Or.inr (hsame_trans (hsame_symm same) rowGap),
              unary_transport source.right same⟩
    · intro row source
      exact ⟨source.left, recognitionLedgerGap⟩
    · intro _row _source
      exact ⟨endpointPkg, observerRouteEndpoint, stateRouteEndpoint⟩
  exact
    ⟨cert, ledgerConsumerUnary, gapConsumerUnary, observerRouteEndpoint, stateRouteEndpoint,
      recognitionLedgerGap, endpointPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
