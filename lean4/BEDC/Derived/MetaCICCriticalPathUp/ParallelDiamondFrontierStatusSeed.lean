import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICParallelDiamondFrontierStatusSeed [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal diamondRead budgetRead endpointRead envelopeRead
      retainedRead statusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock discharge
        handoff continuation provenance localName dyadic stream regseq realSeal bundle pkg →
      Cont continuation localName diamondRead →
        Cont diamondRead obstruction budgetRead →
          Cont budgetRead realSeal endpointRead →
            Cont endpointRead handoff envelopeRead →
              Cont envelopeRead handoff retainedRead →
                Cont retainedRead provenance statusRead →
                  PkgSig bundle statusRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row diamondRead ∨ hsame row budgetRead ∨
                            hsame row endpointRead ∨ hsame row envelopeRead ∨
                              hsame row retainedRead ∨ hsame row statusRead ∨
                                hsame row realSeal)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont retainedRead provenance statusRead ∧
                            PkgSig bundle statusRead pkg ∧ PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory endpointRead ∧ UnaryHistory retainedRead ∧
                        UnaryHistory statusRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalDiamond diamondObstructionBudget budgetRealSealEndpoint
    endpointHandoffEnvelope envelopeHandoffRetained retainedProvenanceStatus statusPkg
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
    unary_cont_closed budgetUnary realSealUnary budgetRealSealEndpoint
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed endpointUnary handoffUnary endpointHandoffEnvelope
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed envelopeUnary handoffUnary envelopeHandoffRetained
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed retainedUnary provenanceUnary retainedProvenanceStatus
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diamondRead ∨ hsame row budgetRead ∨ hsame row endpointRead ∨
              hsame row envelopeRead ∨ hsame row retainedRead ∨ hsame row statusRead ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont retainedRead provenance statusRead ∧
              PkgSig bundle statusRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro statusRead ⟨hsame_refl statusRead, statusUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, retainedProvenanceStatus, statusPkg, realSealPkg⟩
  }
  exact ⟨cert, endpointUnary, retainedUnary, statusUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
