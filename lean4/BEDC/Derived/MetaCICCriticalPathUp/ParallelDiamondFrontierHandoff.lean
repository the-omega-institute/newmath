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

theorem MetaCICCriticalPathParallelDiamondFrontierHandoff [AskSetup] [PackageSetup]
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
                        (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateRead ∨ hsame row frontierRead ∨
                            hsame row residualRead ∨ hsame row diamondRead ∨
                              hsame row l10Read ∨ hsame row endpoint)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont candidateRead handoff frontierRead ∧
                            Cont frontierRead discharge residualRead ∧
                              Cont residualRead obstruction diamondRead ∧
                                Cont diamondRead realSeal l10Read ∧
                                  Cont l10Read provenance endpoint ∧
                                    PkgSig bundle endpoint pkg)
                        hsame ∧
                      UnaryHistory frontierRead ∧ UnaryHistory residualRead ∧
                        UnaryHistory diamondRead ∧ UnaryHistory l10Read ∧
                          UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateHandoffFrontier frontierDischargeResidual
    residualObstructionDiamond diamondRealSealL10 l10ProvenanceEndpoint endpointPkg
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
  have sourceEndpoint :
      (fun row : BHist => hsame row endpoint ∧ UnaryHistory row) endpoint := by
    exact ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨
              hsame row residualRead ∨ hsame row diamondRead ∨
                hsame row l10Read ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidateRead handoff frontierRead ∧
              Cont frontierRead discharge residualRead ∧
                Cont residualRead obstruction diamondRead ∧
                  Cont diamondRead realSeal l10Read ∧
                    Cont l10Read provenance endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
      exact
        ⟨source.right, candidateHandoffFrontier, frontierDischargeResidual,
          residualObstructionDiamond, diamondRealSealL10, l10ProvenanceEndpoint,
          endpointPkg⟩
  }
  exact ⟨cert, frontierUnary, residualUnary, diamondUnary, l10Unary, endpointUnary⟩

theorem MetaCICCriticalPathMatureL10ParallelDiamondRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead residualRead
      diamondRead l10Read endpoint maturityRead : BHist}
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
                    PkgSig bundle maturityRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row maturityRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row candidateRead ∨ hsame row frontierRead ∨
                              hsame row residualRead ∨ hsame row diamondRead ∨
                                hsame row l10Read ∨ hsame row endpoint ∨
                                  hsame row maturityRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont candidateRead handoff frontierRead ∧
                              Cont frontierRead discharge residualRead ∧
                                Cont residualRead obstruction diamondRead ∧
                                  Cont diamondRead realSeal l10Read ∧
                                    Cont l10Read provenance endpoint ∧
                                      Cont endpoint realSeal maturityRead ∧
                                        PkgSig bundle maturityRead pkg)
                          hsame ∧
                        UnaryHistory maturityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateHandoffFrontier frontierDischargeResidual
    residualObstructionDiamond diamondRealSealL10 l10ProvenanceEndpoint
    endpointRealSealMaturity maturityPkg
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
  have sourceMaturity :
      (fun row : BHist => hsame row maturityRead ∧ UnaryHistory row) maturityRead := by
    exact ⟨hsame_refl maturityRead, maturityUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row maturityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨
              hsame row residualRead ∨ hsame row diamondRead ∨
                hsame row l10Read ∨ hsame row endpoint ∨ hsame row maturityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidateRead handoff frontierRead ∧
              Cont frontierRead discharge residualRead ∧
                Cont residualRead obstruction diamondRead ∧
                  Cont diamondRead realSeal l10Read ∧
                    Cont l10Read provenance endpoint ∧
                      Cont endpoint realSeal maturityRead ∧ PkgSig bundle maturityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro maturityRead sourceMaturity
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
      exact
        ⟨source.right, candidateHandoffFrontier, frontierDischargeResidual,
          residualObstructionDiamond, diamondRealSealL10, l10ProvenanceEndpoint,
          endpointRealSealMaturity, maturityPkg⟩
  }
  exact ⟨cert, maturityUnary⟩

theorem MetaCICCriticalPathResidualDiamondCandidateReadbackRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead residualRead
      diamondRead l10Read endpoint maturityRead readback : BHist}
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
                      PkgSig bundle readback pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row candidateRead ∨ hsame row frontierRead ∨
                                hsame row residualRead ∨ hsame row diamondRead ∨
                                  hsame row l10Read ∨ hsame row maturityRead ∨
                                    hsame row readback)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont maturityRead handoff readback ∧
                                PkgSig bundle readback pkg)
                            hsame ∧
                          UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateHandoffFrontier frontierDischargeResidual
    residualObstructionDiamond diamondRealSealL10 l10ProvenanceEndpoint
    endpointRealSealMaturity maturityHandoffReadback readbackPkg
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
  have sourceReadback :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback := by
    exact ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨
              hsame row residualRead ∨ hsame row diamondRead ∨
                hsame row l10Read ∨ hsame row maturityRead ∨ hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont maturityRead handoff readback ∧
              PkgSig bundle readback pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceReadback
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
      exact ⟨source.right, maturityHandoffReadback, readbackPkg⟩
  }
  exact ⟨cert, readbackUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
