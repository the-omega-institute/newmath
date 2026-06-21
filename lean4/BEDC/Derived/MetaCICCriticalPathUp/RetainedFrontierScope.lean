import BEDC.Derived.MetaCICCriticalPathUp.ParallelDiamondFrontierHandoff

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICParallelDiamondRetainedFrontierScope [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead residualRead
      diamondRead l10Read endpoint maturityRead readback targetRead envelopeRead
      retainedRead : BHist}
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
                  Cont endpoint realSeal maturityRead →
                    Cont maturityRead handoff readback →
                      Cont readback provenance targetRead →
                        Cont targetRead obstruction envelopeRead →
                          Cont envelopeRead handoff retainedRead →
                            PkgSig bundle retainedRead pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row retainedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row residualRead ∨ hsame row diamondRead ∨
                                      hsame row l10Read ∨ hsame row targetRead ∨
                                        hsame row envelopeRead ∨ hsame row retainedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      Cont envelopeRead handoff retainedRead ∧
                                        PkgSig bundle retainedRead pkg)
                                  hsame ∧
                                UnaryHistory retainedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateHandoffFrontier frontierDischargeResidual
    residualObstructionDiamond diamondRealSealL10 l10ProvenanceEndpoint
    endpointRealSealMaturity maturityHandoffReadback readbackProvenanceTarget
    targetObstructionEnvelope envelopeHandoffRetained retainedPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
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
  have maturityUnary : UnaryHistory maturityRead :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealMaturity
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed maturityUnary handoffUnary maturityHandoffReadback
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceTarget
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed targetUnary obstructionUnary targetObstructionEnvelope
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed envelopeUnary handoffUnary envelopeHandoffRetained
  have sourceRetained :
      (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row) retainedRead := by
    exact ⟨hsame_refl retainedRead, retainedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row diamondRead ∨ hsame row l10Read ∨
              hsame row targetRead ∨ hsame row envelopeRead ∨ hsame row retainedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont envelopeRead handoff retainedRead ∧
              PkgSig bundle retainedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro retainedRead sourceRetained
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
      exact ⟨source.right, envelopeHandoffRetained, retainedPkg⟩
  }
  exact ⟨cert, retainedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
