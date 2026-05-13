import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ∧
              hsame row provenance)
          (fun _row : BHist =>
            UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
              Cont precision endpoint window)
          (fun row : BHist => PkgSig bundle row pkg ∧ Cont window ledger provenance)
          hsame ∧
        PkgSig bundle provenance pkg := by
  intro carrier
  have carrierData :
      DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg :=
    carrier
  obtain ⟨precisionUnary, endpointUnary, windowUnary, _ledgerUnary, _provenanceUnary,
    precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ∧
              hsame row provenance)
          (fun _row : BHist =>
            UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
              Cont precision endpoint window)
          (fun row : BHist => PkgSig bundle row pkg ∧ Cont window ledger provenance)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨carrierData, hsame_refl provenance⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro _row _sourceRow
      exact ⟨precisionUnary, endpointUnary, windowUnary, precisionEndpointWindow⟩
    ledger_sound := by
      intro row sourceRow
      cases sourceRow.right
      exact ⟨provenancePkg, windowLedgerProvenance⟩
  }
  exact ⟨cert, provenancePkg⟩

theorem DyadicApproximationCarrier_streamname_real_seal_factorization_certificate
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance streamWindow readback dyadic realSeal
      diagonalSelector finiteSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      UnaryHistory streamWindow ->
        UnaryHistory dyadic ->
          UnaryHistory diagonalSelector ->
            Cont window streamWindow readback ->
              Cont readback dyadic realSeal ->
                Cont realSeal diagonalSelector finiteSurface ->
                  PkgSig bundle finiteSurface pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row finiteSurface ∧ UnaryHistory row)
                      (fun _row : BHist =>
                        Cont realSeal diagonalSelector finiteSurface ∧
                          PkgSig bundle finiteSurface pkg)
                      (fun _row : BHist =>
                        DyadicApproximationCarrier precision endpoint window ledger provenance
                            bundle pkg ∧
                          UnaryHistory streamWindow ∧ UnaryHistory readback ∧
                            UnaryHistory realSeal)
                      hsame := by
  intro carrier streamWindowUnary dyadicUnary diagonalSelectorUnary
  intro windowStreamReadback readbackDyadicRealSeal realSealDiagonalFiniteSurface finitePkg
  have carrierData :
      DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg :=
    carrier
  obtain ⟨_precisionUnary, _endpointUnary, windowUnary, _ledgerUnary, _provenanceUnary,
    _precisionEndpointWindow, _windowLedgerProvenance, _provenancePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary streamWindowUnary windowStreamReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicRealSeal
  have finiteSurfaceUnary : UnaryHistory finiteSurface :=
    unary_cont_closed realSealUnary diagonalSelectorUnary realSealDiagonalFiniteSurface
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro finiteSurface ⟨hsame_refl finiteSurface, finiteSurfaceUnary⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row _sourceRow
      exact ⟨realSealDiagonalFiniteSurface, finitePkg⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨carrierData, streamWindowUnary, readbackUnary, realSealUnary⟩
  }

end BEDC.Derived.DyadicApproximationUp
