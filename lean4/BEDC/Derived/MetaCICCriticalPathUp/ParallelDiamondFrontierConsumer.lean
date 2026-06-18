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

theorem MetaCICCriticalPathDiamondFrontierConsumer [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal diamondRead budgetRead endpointRead frontierRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName diamondRead →
        Cont diamondRead obstruction budgetRead →
          Cont budgetRead realSeal endpointRead →
            Cont endpointRead handoff frontierRead →
              Cont frontierRead provenance consumerRead →
                PkgSig bundle consumerRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row diamondRead ∨ hsame row budgetRead ∨
                          hsame row endpointRead ∨ hsame row frontierRead ∨
                            hsame row consumerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle consumerRead pkg ∧
                          PkgSig bundle realSeal pkg)
                      hsame ∧
                    UnaryHistory diamondRead ∧ UnaryHistory budgetRead ∧
                      UnaryHistory endpointRead ∧ UnaryHistory frontierRead ∧
                        UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalDiamond diamondObstructionBudget budgetRealEndpoint
    endpointHandoffFrontier frontierProvenanceConsumer consumerPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalDiamond
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed diamondUnary obstructionUnary diamondObstructionBudget
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary realSealUnary budgetRealEndpoint
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed endpointUnary handoffUnary endpointHandoffFrontier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed frontierUnary provenanceUnary frontierProvenanceConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diamondRead ∨ hsame row budgetRead ∨
              hsame row endpointRead ∨ hsame row frontierRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle consumerRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, consumerPkg, realSealPkg⟩
  }
  exact
    ⟨cert, diamondUnary, budgetUnary, endpointUnary, frontierUnary, consumerUnary⟩

theorem MetaCICCriticalPathFrontierConsumerNonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal diamondRead budgetRead endpointRead frontierRead
      socketRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName diamondRead →
        Cont diamondRead obstruction budgetRead →
          Cont budgetRead realSeal endpointRead →
            Cont endpointRead handoff frontierRead →
              Cont frontierRead obstruction socketRead →
                Cont socketRead provenance consumerRead →
                  PkgSig bundle consumerRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row frontierRead ∨ hsame row socketRead ∨
                            hsame row consumerRead ∨ hsame row dyadic ∨ hsame row stream ∨
                              hsame row regseq ∨ hsame row realSeal)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont frontierRead obstruction socketRead ∧
                            PkgSig bundle consumerRead pkg ∧ PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory frontierRead ∧ UnaryHistory socketRead ∧
                        UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalDiamond diamondObstructionBudget budgetRealEndpoint
    endpointHandoffFrontier frontierObstructionSocket socketProvenanceConsumer consumerPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalDiamond
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed diamondUnary obstructionUnary diamondObstructionBudget
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary realSealUnary budgetRealEndpoint
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed endpointUnary handoffUnary endpointHandoffFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed socketUnary provenanceUnary socketProvenanceConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontierRead ∨ hsame row socketRead ∨ hsame row consumerRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontierRead obstruction socketRead ∧
              PkgSig bundle consumerRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
      exact ⟨source.right, frontierObstructionSocket, consumerPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, socketUnary, consumerUnary⟩

theorem MetaCICCriticalPathResidualHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal diamondRead budgetRead endpointRead frontierRead
      residualRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName diamondRead →
        Cont diamondRead obstruction budgetRead →
          Cont budgetRead realSeal endpointRead →
            Cont endpointRead handoff frontierRead →
              Cont frontierRead obstruction residualRead →
                Cont residualRead provenance consumerRead →
                  PkgSig bundle consumerRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row diamondRead ∨ hsame row budgetRead ∨
                            hsame row endpointRead ∨ hsame row frontierRead ∨
                              hsame row residualRead ∨ hsame row consumerRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont frontierRead obstruction residualRead ∧
                            PkgSig bundle consumerRead pkg ∧ PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory residualRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalDiamond diamondObstructionBudget budgetRealEndpoint
    endpointHandoffFrontier frontierObstructionResidual residualProvenanceConsumer consumerPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalDiamond
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed diamondUnary obstructionUnary diamondObstructionBudget
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary realSealUnary budgetRealEndpoint
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed endpointUnary handoffUnary endpointHandoffFrontier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionResidual
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed residualUnary provenanceUnary residualProvenanceConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diamondRead ∨ hsame row budgetRead ∨ hsame row endpointRead ∨
              hsame row frontierRead ∨ hsame row residualRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontierRead obstruction residualRead ∧
              PkgSig bundle consumerRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
      exact ⟨source.right, frontierObstructionResidual, consumerPkg, realSealPkg⟩
  }
  exact ⟨cert, residualUnary, consumerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
