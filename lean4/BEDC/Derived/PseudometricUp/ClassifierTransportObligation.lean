import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_classifier_transport_obligation [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName pointRead
      distanceRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      hsame pointRead point ->
        hsame distanceRead distance ->
          Cont pointRead distanceRead replayRead ->
            PkgSig bundle replayRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row point ∨ hsame row distance ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle replayRead pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory pointRead ∧ UnaryHistory distanceRead ∧
                  UnaryHistory replayRead ∧ Cont pointRead distanceRead replayRead ∧
                    PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier samePoint sameDistance pointDistanceReplay replayPkg
  obtain ⟨pointUnary, distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, _zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    _streamReadbackDyadic, _dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have pointReadUnary : UnaryHistory pointRead :=
    unary_transport pointUnary (hsame_symm samePoint)
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_transport distanceUnary (hsame_symm sameDistance)
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed pointReadUnary distanceReadUnary pointDistanceReplay
  have sourceReplay :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayReadUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro replayRead sourceReplay
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
        have sameOtherReplay : hsame other replayRead :=
          hsame_trans (hsame_symm sameRows) sourceRow.left
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right sameRows
        exact ⟨sameOtherReplay, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row distance ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle replayRead pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr sourceRow.left)
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, replayPkg, localNamePkg⟩
    }
  exact
    ⟨cert, pointReadUnary, distanceReadUnary, replayReadUnary, pointDistanceReplay,
      localNamePkg⟩

end BEDC.Derived.PseudometricUp
