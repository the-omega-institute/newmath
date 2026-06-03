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

theorem MetaCICCriticalPathSNDischargeFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont strongNorm normalForm frontier ->
        Cont discharge frontier obstruction ->
          PkgSig bundle frontier pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row discharge ∨ hsame row frontier ∨ hsame row dyadic ∨
                      hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
                    Cont strongNorm normalForm frontier)
                hsame ∧
              UnaryHistory frontier := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledger strongNormalFrontier _dischargeFrontierObstruction frontierPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormalFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row frontier ∧ UnaryHistory row) frontier := by
    exact ⟨hsame_refl frontier, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row discharge ∨ hsame row frontier ∨ hsame row dyadic ∨
                hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
              Cont strongNorm normalForm frontier)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontier sourceFrontier
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, strongNormalFrontier⟩
  }
  exact ⟨cert, frontierUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
