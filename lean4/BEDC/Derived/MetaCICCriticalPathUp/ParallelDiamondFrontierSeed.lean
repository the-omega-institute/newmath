import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathParallelDiamondFrontierSeed [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal diamondRead budgetRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName diamondRead →
        Cont diamondRead obstruction budgetRead →
          Cont budgetRead realSeal endpointRead →
            PkgSig bundle endpointRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row diamondRead ∨
                        hsame row budgetRead ∨ hsame row endpointRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont budgetRead realSeal endpointRead ∧
                      PkgSig bundle endpointRead pkg ∧ PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory diamondRead ∧ UnaryHistory budgetRead ∧
                  UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameDiamond diamondObstructionBudget budgetRealSealEndpoint
    endpointPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameDiamond
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed diamondUnary obstructionUnary diamondObstructionBudget
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary realSealUnary budgetRealSealEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row diamondRead ∨ hsame row budgetRead ∨
                hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont budgetRead realSeal endpointRead ∧
              PkgSig bundle endpointRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
      exact ⟨source.right, budgetRealSealEndpoint, endpointPkg, realSealPkg⟩
  }
  exact ⟨cert, diamondUnary, budgetUnary, endpointUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
