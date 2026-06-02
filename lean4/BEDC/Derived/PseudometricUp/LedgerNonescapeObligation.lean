import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_ledger_nonescape_obligation [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName ledgerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont zeroRow replay ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row zeroRow ∨ hsame row ledgerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle ledgerRead pkg ∧
                  PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory ledgerRead ∧ Cont stream readback dyadic ∧
              Cont dyadic sealRow zeroRow ∧ Cont zeroRow replay ledgerRead ∧
                PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier zeroReplayLedger ledgerPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, _transportUnary, replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed zeroUnary replayUnary zeroReplayLedger
  have sourceLedger :
      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) ledgerRead := by
    exact ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro ledgerRead sourceLedger
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows sourceRow
        have sameOtherLedger : hsame other ledgerRead :=
          hsame_trans (hsame_symm sameRows) sourceRow.left
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right sameRows
        exact ⟨sameOtherLedger, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row zeroRow ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle ledgerRead pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr sourceRow.left)
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, ledgerPkg, localNamePkg⟩
    }
  exact
    ⟨cert, ledgerUnary, streamReadbackDyadic, dyadicSealZero, zeroReplayLedger, localNamePkg⟩

theorem PseudometricCarrier_boundary_ledger_nonescape_consumer [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      zeroBoundaryRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont zeroRow transport zeroBoundaryRead ->
        PkgSig bundle zeroBoundaryRead pkg ->
          Cont zeroBoundaryRead replay ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row zeroBoundaryRead ∨ hsame row replay ∨ hsame row ledgerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle zeroBoundaryRead pkg ∧
                      PkgSig bundle ledgerRead pkg ∧ PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory zeroBoundaryRead ∧ UnaryHistory ledgerRead ∧
                  Cont stream readback dyadic ∧ Cont dyadic sealRow zeroRow ∧
                    Cont zeroBoundaryRead replay ledgerRead ∧ PkgSig bundle localName pkg := by
  intro carrier zeroTransportBoundary boundaryPkg boundaryReplayLedger ledgerPkg
  have boundarySurface :=
    PseudometricCarrier_zero_distance_boundary_obligation carrier zeroTransportBoundary
      boundaryPkg
  obtain ⟨_boundaryCert, boundaryUnary, streamReadbackDyadic, dyadicSealZero, localNamePkg⟩ :=
    boundarySurface
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, _zeroUnary, _transportUnary, replayUnary, _localNameUnary,
    _streamReadbackDyadic, _dyadicSealZero, _localNameZero, _localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundaryUnary replayUnary boundaryReplayLedger
  have sourceLedger :
      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) ledgerRead := by
    exact ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro ledgerRead sourceLedger
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroBoundaryRead ∨ hsame row replay ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle zeroBoundaryRead pkg ∧
              PkgSig bundle ledgerRead pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := core
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, boundaryPkg, ledgerPkg, localNamePkg⟩
  }
  exact
    ⟨cert, boundaryUnary, ledgerUnary, streamReadbackDyadic, dyadicSealZero,
      boundaryReplayLedger, localNamePkg⟩

end BEDC.Derived.PseudometricUp
