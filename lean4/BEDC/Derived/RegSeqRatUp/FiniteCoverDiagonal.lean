import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatFiniteCoverDiagonalRealSealExhaustion [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback realSeal diagonal
      terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      UnaryHistory realSeal ->
        Cont readback realSeal diagonal ->
          Cont diagonal endpoint terminal ->
            PkgSig bundle terminal pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row schedule ∨ hsame row endpoint ∨ hsame row readback ∨
                      hsame row realSeal ∨ hsame row diagonal ∨ hsame row terminal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont readback realSeal diagonal ∧
                      Cont diagonal endpoint terminal ∧ PkgSig bundle terminal pkg)
                  hsame ∧
                UnaryHistory diagonal ∧ UnaryHistory terminal ∧ PkgSig bundle readback pkg ∧
                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier realSealUnary readbackRealSealDiagonal diagonalEndpointTerminal terminalPkg
  obtain ⟨_scheduleUnary, _indexUnary, endpointUnary, _radiusUnary, _regularityUnary,
    _provenanceUnary, readbackUnary, _scheduleIndexEndpoint, _endpointRadiusRegularity,
    _regularityProvenanceReadback, readbackPkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealDiagonal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed diagonalUnary endpointUnary diagonalEndpointTerminal
  have sourceTerminal :
      (fun row : BHist => hsame row terminal ∧ UnaryHistory row) terminal := by
    exact ⟨hsame_refl terminal, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row endpoint ∨ hsame row readback ∨
              hsame row realSeal ∨ hsame row diagonal ∨ hsame row terminal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readback realSeal diagonal ∧
              Cont diagonal endpoint terminal ∧ PkgSig bundle terminal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal sourceTerminal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, readbackRealSealDiagonal, diagonalEndpointTerminal,
          terminalPkg⟩
  }
  exact ⟨cert, diagonalUnary, terminalUnary, readbackPkg, terminalPkg⟩

end BEDC.Derived.RegSeqRatUp
