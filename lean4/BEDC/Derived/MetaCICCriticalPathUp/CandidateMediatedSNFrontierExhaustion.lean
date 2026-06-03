import BEDC.Derived.MetaCICCriticalPathUp.CandidateMediatedSNFrontier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNFrontierExhaustion [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier residualSocket confluenceBudget
      decidabilityRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier discharge residualSocket →
          Cont residualSocket handoff confluenceBudget →
            Cont confluenceBudget realSeal decidabilityRead →
              Cont decidabilityRead localName publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row frontier ∨ hsame row residualSocket ∨
                          hsame row confluenceBudget ∨ hsame row decidabilityRead ∨
                            hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
                          PkgSig bundle realSeal pkg ∧
                            Cont frontier discharge residualSocket)
                      hsame ∧
                    UnaryHistory frontier ∧ UnaryHistory residualSocket ∧
                      UnaryHistory confluenceBudget ∧ UnaryHistory decidabilityRead ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierDischargeResidual residualHandoffConfluence
    confluenceRealSealDecidability decidabilityLocalPublic publicPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have residualUnary : UnaryHistory residualSocket :=
    unary_cont_closed frontierUnary dischargeUnary frontierDischargeResidual
  have confluenceUnary : UnaryHistory confluenceBudget :=
    unary_cont_closed residualUnary handoffUnary residualHandoffConfluence
  have decidabilityUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed confluenceUnary realSealUnary confluenceRealSealDecidability
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decidabilityUnary localNameUnary decidabilityLocalPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row residualSocket ∨ hsame row confluenceBudget ∨
              hsame row decidabilityRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
              PkgSig bundle realSeal pkg ∧ Cont frontier discharge residualSocket)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.right, publicPkg, realSealPkg, frontierDischargeResidual⟩
  }
  exact ⟨cert, frontierUnary, residualUnary, confluenceUnary, decidabilityUnary, publicUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
