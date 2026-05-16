import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_gap_ledger_route [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint
      gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance name endpoint bundle pkg →
      Cont ledger gap gapRead →
        PkgSig bundle gapRead pkg →
          SemanticNameCert
                (fun row : BHist =>
                  ConsciousObserverStateCarrier observer state recognition ledger gap transport
                    route provenance name endpoint bundle pkg ∧ hsame row gap)
                (fun row : BHist =>
                  hsame row gap ∧ UnaryHistory row ∧ Cont ledger gap gapRead)
                (fun _row : BHist =>
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle gapRead pkg ∧
                    Cont observer route endpoint)
                hsame ∧
              UnaryHistory gapRead ∧ Cont recognition ledger gap ∧
              Cont ledger gap gapRead ∧ PkgSig bundle gapRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerGapRead gapReadPkg
  have carrierPacket :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance name endpoint bundle pkg :=
    carrier
  obtain ⟨_observerUnary, _stateUnary, _recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, _stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed ledgerUnary gapUnary ledgerGapRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance name endpoint bundle pkg ∧ hsame row gap)
          (fun row : BHist =>
            hsame row gap ∧ UnaryHistory row ∧ Cont ledger gap gapRead)
          (fun _row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle gapRead pkg ∧
              Cont observer route endpoint)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gap ⟨carrierPacket, hsame_refl gap⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameGap : hsame row gap := source.right
      exact
        ⟨rowSameGap, unary_transport gapUnary (hsame_symm rowSameGap), ledgerGapRead⟩
    · intro _row _source
      exact ⟨endpointPkg, gapReadPkg, observerRouteEndpoint⟩
  exact ⟨cert, gapReadUnary, recognitionLedgerGap, ledgerGapRead, gapReadPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
