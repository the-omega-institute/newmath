import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_gap_scope_binding [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance nameRow endpoint gapRead
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg →
      hsame gapRead gap →
        Cont ledger gap scopeRead →
          PkgSig bundle scopeRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ConsciousObserverStateCarrier observer state recognition ledger gap transport
                      route provenance nameRow endpoint bundle pkg ∧
                    hsame row gap)
                (fun row : BHist =>
                  hsame row gap ∧ UnaryHistory row ∧ Cont ledger gap scopeRead)
                (fun _row : BHist =>
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle scopeRead pkg ∧
                    Cont observer route endpoint)
                hsame ∧
              UnaryHistory gapRead ∧ UnaryHistory scopeRead ∧
                Cont ledger gap scopeRead ∧ Cont observer route endpoint ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gapReadSame ledgerGapScope scopePkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance nameRow endpoint bundle pkg :=
    carrier
  obtain ⟨_observerUnary, _stateUnary, _recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, _stateRouteEndpoint, _recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have gapReadUnary : UnaryHistory gapRead :=
    unary_transport gapUnary (hsame_symm gapReadSame)
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed ledgerUnary gapUnary ledgerGapScope
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport
                route provenance nameRow endpoint bundle pkg ∧
              hsame row gap)
          (fun row : BHist =>
            hsame row gap ∧ UnaryHistory row ∧ Cont ledger gap scopeRead)
          (fun _row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle scopeRead pkg ∧
              Cont observer route endpoint)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gap ⟨carrierPacket, hsame_refl gap⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameGap : hsame row gap := source.right
      exact
        ⟨rowSameGap, unary_transport gapUnary (hsame_symm rowSameGap), ledgerGapScope⟩
    · intro _row _source
      exact ⟨endpointPkg, scopePkg, observerRouteEndpoint⟩
  exact
    ⟨cert, gapReadUnary, scopeUnary, ledgerGapScope, observerRouteEndpoint, endpointPkg,
      scopePkg⟩

end BEDC.Derived.ConsciousObserverStateUp
