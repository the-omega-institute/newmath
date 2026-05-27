import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathClosedSubstitutionBoundaryExposure [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal substitutionBoundary socketBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont handoff continuation substitutionBoundary ->
        Cont discharge obstruction socketBoundary ->
          PkgSig bundle substitutionBoundary pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row substitutionBoundary ∨ hsame row socketBoundary) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row handoff ∨ hsame row continuation ∨ hsame row discharge ∨
                    hsame row obstruction ∨ hsame row substitutionBoundary ∨
                      hsame row socketBoundary)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle substitutionBoundary pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory substitutionBoundary ∧ UnaryHistory socketBoundary ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger handoffContinuationSubstitution dischargeObstructionSocket substitutionPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have substitutionUnary : UnaryHistory substitutionBoundary :=
    unary_cont_closed handoffUnary continuationUnary handoffContinuationSubstitution
  have socketUnary : UnaryHistory socketBoundary :=
    unary_cont_closed dischargeUnary obstructionUnary dischargeObstructionSocket
  have substitutionCarrier :
      (fun row : BHist =>
        (hsame row substitutionBoundary ∨ hsame row socketBoundary) ∧
          UnaryHistory row) substitutionBoundary := by
    exact ⟨Or.inl (hsame_refl substitutionBoundary), substitutionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row substitutionBoundary ∨ hsame row socketBoundary) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row continuation ∨ hsame row discharge ∨
              hsame row obstruction ∨ hsame row substitutionBoundary ∨
                hsame row socketBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle substitutionBoundary pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro substitutionBoundary substitutionCarrier
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
        intro _row _other sameRows source
        cases source.left with
        | inl substitutionSame =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) substitutionSame),
                unary_transport source.right sameRows⟩
        | inr socketSame =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) socketSame),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl substitutionSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl substitutionSame))))
      | inr socketSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr socketSame))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, substitutionPkg, realSealPkg⟩
  }
  exact ⟨cert, substitutionUnary, socketUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
