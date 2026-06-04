import BEDC.Derived.MetaCICCriticalPathUp.CandidateResidualStability

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRealRegularHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualRead dyadicRead streamRead regseqRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathCandidateMediatedFrontier strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont handoff discharge residualRead →
        Cont residualRead dyadic dyadicRead →
          Cont dyadicRead stream streamRead →
            Cont streamRead regseq regseqRead →
              Cont regseqRead realSeal realRead →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row residualRead ∨ hsame row dyadicRead ∨
                          hsame row streamRead ∨ hsame row regseqRead ∨
                            hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont residualRead dyadic dyadicRead ∧
                          Cont dyadicRead stream streamRead ∧
                            Cont streamRead regseq regseqRead ∧
                              Cont regseqRead realSeal realRead ∧
                                PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                      UnaryHistory regseqRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontier handoffDischargeResidual residualDyadicRead dyadicStreamRead
    streamRegseqRead regseqRealRead realReadPkg
  obtain ⟨ledger, _dyadicFrontierUnary, _streamFrontierUnary, _regseqFrontierUnary,
    _realSealFrontierUnary⟩ := frontier
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary dischargeUnary handoffDischargeResidual
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed residualUnary dyadicUnary residualDyadicRead
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicReadUnary streamUnary dyadicStreamRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamReadUnary regseqUnary streamRegseqRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary realSealUnary regseqRealRead
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row dyadicRead ∨ hsame row streamRead ∨
              hsame row regseqRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont residualRead dyadic dyadicRead ∧
              Cont dyadicRead stream streamRead ∧ Cont streamRead regseq regseqRead ∧
                Cont regseqRead realSeal realRead ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact
        ⟨source.right, residualDyadicRead, dyadicStreamRead, streamRegseqRead,
          regseqRealRead, realReadPkg⟩
  }
  exact ⟨cert, dyadicReadUnary, streamReadUnary, regseqReadUnary, realReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
