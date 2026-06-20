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

theorem MetaCICCriticalPathL10SourceLedgerReadback [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal diamondRead budgetRead endpointRead frontierRead
      residualRead witnessRead sourceLedgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName diamondRead →
        Cont diamondRead obstruction budgetRead →
          Cont budgetRead realSeal endpointRead →
            Cont endpointRead handoff frontierRead →
              Cont frontierRead discharge residualRead →
                Cont residualRead obstruction witnessRead →
                  Cont witnessRead realSeal sourceLedgerRead →
                    PkgSig bundle sourceLedgerRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row sourceLedgerRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                              hsame row realSeal ∨ hsame row residualRead ∨
                                hsame row witnessRead ∨ hsame row sourceLedgerRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont witnessRead realSeal sourceLedgerRead ∧
                              PkgSig bundle sourceLedgerRead pkg ∧
                                PkgSig bundle realSeal pkg)
                          hsame ∧
                        UnaryHistory sourceLedgerRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro ledger continuationLocalNameDiamond diamondObstructionBudget budgetRealEndpoint
    endpointHandoffFrontier frontierDischargeResidual residualObstructionWitness
    witnessRealSource sourceLedgerPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameDiamond
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed diamondUnary obstructionUnary diamondObstructionBudget
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary realSealUnary budgetRealEndpoint
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed endpointUnary handoffUnary endpointHandoffFrontier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary dischargeUnary frontierDischargeResidual
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionWitness
  have sourceLedgerUnary : UnaryHistory sourceLedgerRead :=
    unary_cont_closed witnessUnary realSealUnary witnessRealSource
  have sourceLedger :
      (fun row : BHist => hsame row sourceLedgerRead ∧ UnaryHistory row) sourceLedgerRead := by
    exact ⟨hsame_refl sourceLedgerRead, sourceLedgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceLedgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
              hsame row residualRead ∨ hsame row witnessRead ∨ hsame row sourceLedgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont witnessRead realSeal sourceLedgerRead ∧
              PkgSig bundle sourceLedgerRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceLedgerRead sourceLedger
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
      exact ⟨source.right, witnessRealSource, sourceLedgerPkg, realSealPkg⟩
  }
  exact ⟨cert, sourceLedgerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
