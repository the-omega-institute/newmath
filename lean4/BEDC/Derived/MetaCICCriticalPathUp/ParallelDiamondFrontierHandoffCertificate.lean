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

theorem MetaCICCriticalPathParallelDiamondFrontierHandoffCertificate [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead residualRead
      diamondRead l10Read endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff frontierRead →
          Cont frontierRead discharge residualRead →
            Cont residualRead obstruction diamondRead →
              Cont diamondRead realSeal l10Read →
                Cont l10Read provenance endpoint →
                  PkgSig bundle endpoint pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          (hsame row endpoint ∨ hsame row dyadic ∨ hsame row stream ∨
                            hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateRead ∨ hsame row frontierRead ∨
                            hsame row residualRead ∨ hsame row diamondRead ∨
                              hsame row l10Read ∨ hsame row endpoint ∨ hsame row dyadic ∨
                                hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧
                            PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory frontierRead ∧ UnaryHistory residualRead ∧
                        UnaryHistory diamondRead ∧ UnaryHistory l10Read ∧
                          UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateHandoffFrontier frontierDischargeResidual
    residualObstructionDiamond diamondRealSealL10 l10ProvenanceEndpoint endpointPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFrontier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary dischargeUnary frontierDischargeResidual
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionDiamond
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed diamondUnary realSealUnary diamondRealSealL10
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed l10Unary provenanceUnary l10ProvenanceEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row endpoint ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨
              hsame row residualRead ∨ hsame row diamondRead ∨ hsame row l10Read ∨
                hsame row endpoint ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint
        ⟨Or.inl (hsame_refl endpoint), endpointUnary⟩
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
        exact ⟨by
          cases source.left with
          | inl sameEndpoint =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)
          | inr rest =>
              cases rest with
              | inl sameDyadic =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic))
              | inr rest =>
                  cases rest with
                  | inl sameStream =>
                      exact Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameStream)))
                  | inr rest =>
                      cases rest with
                      | inl sameRegseq =>
                          exact Or.inr (Or.inr (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameRegseq))))
                      | inr sameRealSeal =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr
                            (hsame_trans (hsame_symm sameRows) sameRealSeal))))
          , unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEndpoint =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameEndpoint)))))
      | inr rest =>
          cases rest with
          | inl sameDyadic =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl sameDyadic))))))
          | inr rest =>
              cases rest with
              | inl sameStream =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inl sameStream)))))))
              | inr rest =>
                  cases rest with
                  | inl sameRegseq =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inl sameRegseq))))))))
                  | inr sameRealSeal =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr sameRealSeal))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, residualUnary, diamondUnary, l10Unary, endpointUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
