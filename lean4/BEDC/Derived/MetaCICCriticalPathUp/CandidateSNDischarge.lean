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

theorem MetaCICCriticalPathCandidateSNDischarge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead faceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation realSeal candidateRead →
        Cont candidateRead discharge faceRead →
          PkgSig bundle faceRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row faceRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row discharge ∨ hsame row faceRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle faceRead pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory candidateRead ∧ UnaryHistory faceRead ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationRealSealCandidate candidateDischargeFace faceReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary realSealUnary continuationRealSealCandidate
  have faceUnary : UnaryHistory faceRead :=
    unary_cont_closed candidateUnary dischargeUnary candidateDischargeFace
  have sourceFace :
      (fun row : BHist => hsame row faceRead ∧ UnaryHistory row) faceRead := by
    exact ⟨hsame_refl faceRead, faceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row faceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row discharge ∨ hsame row faceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle faceRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro faceRead sourceFace
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, faceReadPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, faceUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
