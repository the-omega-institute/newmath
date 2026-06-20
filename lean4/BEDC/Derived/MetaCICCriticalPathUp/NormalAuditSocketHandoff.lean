import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathNormalAuditSocketHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal closedTerm candidate closedCandidate candidateSet
      socketObstruction socketFrontier socketReplay socketProvenance criticalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont closedTerm candidate socketReplay →
        Cont socketReplay socketFrontier criticalRead →
          Cont criticalRead provenance realSeal →
            PkgSig bundle criticalRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row criticalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row closedTerm ∨ hsame row candidate ∨ hsame row closedCandidate ∨
                      hsame row candidateSet ∨ hsame row socketObstruction ∨
                        hsame row socketFrontier ∨ hsame row criticalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont closedTerm candidate socketReplay ∧
                      Cont socketReplay socketFrontier criticalRead ∧
                        PkgSig bundle criticalRead pkg)
                  hsame ∧
                UnaryHistory criticalRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro ledger closedTermCandidateReplay replayFrontierCritical criticalProvenanceReal
    criticalPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have criticalUnaryFromSeal : UnaryHistory criticalRead :=
    unary_cont_left_factor criticalProvenanceReal realSealUnary
  have sourceCritical :
      (fun row : BHist => hsame row criticalRead ∧ UnaryHistory row) criticalRead := by
    exact ⟨hsame_refl criticalRead, criticalUnaryFromSeal⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row criticalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closedTerm ∨ hsame row candidate ∨ hsame row closedCandidate ∨
              hsame row candidateSet ∨ hsame row socketObstruction ∨
                hsame row socketFrontier ∨ hsame row criticalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont closedTerm candidate socketReplay ∧
              Cont socketReplay socketFrontier criticalRead ∧ PkgSig bundle criticalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro criticalRead sourceCritical
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, closedTermCandidateReplay, replayFrontierCritical, criticalPkg⟩
  }
  exact ⟨cert, criticalUnaryFromSeal⟩

end BEDC.Derived.MetaCICCriticalPathUp
