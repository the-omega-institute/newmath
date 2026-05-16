import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_present_ledger_boundary [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint ledgerRead
      gapRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg →
      hsame ledgerRead ledger →
        hsame gapRead gap →
          Cont ledgerRead gapRead boundaryRead →
            PkgSig bundle boundaryRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row boundaryRead ∧ Cont ledgerRead gapRead boundaryRead)
                  (fun _row : BHist =>
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory ledgerRead ∧ UnaryHistory gapRead ∧
                  UnaryHistory boundaryRead ∧ Cont ledgerRead gapRead boundaryRead ∧
                    Cont observer route endpoint ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sameLedgerRead sameGapRead ledgerGapBoundary boundaryPkg
  obtain ⟨_observerUnary, _stateUnary, _recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    observerRouteEndpoint, _stateRouteEndpoint, _recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_transport_symm ledgerUnary sameLedgerRead
  have gapReadUnary : UnaryHistory gapRead :=
    unary_transport_symm gapUnary sameGapRead
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerReadUnary gapReadUnary ledgerGapBoundary
  have boundarySource :
      hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont ledgerRead gapRead boundaryRead)
          (fun _row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead boundarySource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        have row'SameBoundary : hsame row' boundaryRead :=
          hsame_trans (hsame_symm sameRows) source.left
        exact
          ⟨row'SameBoundary,
            unary_transport boundaryUnary (hsame_symm row'SameBoundary)⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨source.left, ledgerGapBoundary⟩
    ledger_sound := by
      intro _row _source
      exact ⟨endpointPkg, boundaryPkg⟩
  }
  exact
    ⟨cert, ledgerReadUnary, gapReadUnary, boundaryUnary, ledgerGapBoundary,
      observerRouteEndpoint, endpointPkg, boundaryPkg⟩

end BEDC.Derived.ConsciousObserverStateUp
