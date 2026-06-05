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

theorem MetaCICCriticalPathBridgeBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead confluenceRead residualRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff confluenceRead →
          Cont confluenceRead obstruction residualRead →
            Cont residualRead discharge bridgeRead →
              PkgSig bundle bridgeRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row confluenceRead ∨
                        hsame row residualRead ∨ hsame row obstruction ∨
                          hsame row discharge ∨ hsame row bridgeRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont candidateRead handoff confluenceRead ∧
                        Cont confluenceRead obstruction residualRead ∧
                          Cont residualRead discharge bridgeRead ∧
                            PkgSig bundle bridgeRead pkg)
                    hsame ∧
                  UnaryHistory residualRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateHandoffConfluence
    confluenceObstructionResidual residualDischargeBridge bridgePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffConfluence
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed confluenceUnary obstructionUnary confluenceObstructionResidual
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed residualUnary dischargeUnary residualDischargeBridge
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row confluenceRead ∨ hsame row residualRead ∨
              hsame row obstruction ∨ hsame row discharge ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidateRead handoff confluenceRead ∧
              Cont confluenceRead obstruction residualRead ∧
                Cont residualRead discharge bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
        ⟨source.right, candidateHandoffConfluence, confluenceObstructionResidual,
          residualDischargeBridge, bridgePkg⟩
  }
  exact ⟨cert, residualUnary, bridgeUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
