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

theorem MetaCICCriticalPathCandidateSNConfluenceHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateFrontier confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateFrontier →
        Cont candidateFrontier handoff confluenceRead →
          PkgSig bundle confluenceRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row continuation ∨ hsame row candidateFrontier ∨
                    hsame row confluenceRead ∨ hsame row handoff ∨
                      hsame row obstruction ∨ hsame row discharge ∨ hsame row dyadic ∨
                        hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont continuation localName candidateFrontier ∧
                    Cont candidateFrontier handoff confluenceRead ∧
                      PkgSig bundle confluenceRead pkg ∧ PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory candidateFrontier ∧ UnaryHistory confluenceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateHandoffConfluence confluenceReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateFrontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalCandidate
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffConfluence
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row continuation ∨ hsame row candidateFrontier ∨
              hsame row confluenceRead ∨ hsame row handoff ∨ hsame row obstruction ∨
                hsame row discharge ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuation localName candidateFrontier ∧
              Cont candidateFrontier handoff confluenceRead ∧
                PkgSig bundle confluenceRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro confluenceRead
        ⟨hsame_refl confluenceRead, confluenceUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, continuationLocalCandidate, candidateHandoffConfluence,
          confluenceReadPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, confluenceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
