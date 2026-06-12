import BEDC.Derived.MetaCICCriticalPathUp.CandidateMediatedSNFrontierExhaustion

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNBudgetExtraction [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead sourceRead residualRead witnessRead
      fairnessRead transportRead replayRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock discharge
        handoff continuation provenance localName dyadic stream regseq realSeal bundle pkg ->
      Cont continuation localName candidateRead ->
        Cont candidateRead stream sourceRead ->
          Cont sourceRead obstruction residualRead ->
            Cont residualRead discharge witnessRead ->
              Cont witnessRead handoff fairnessRead ->
                Cont fairnessRead continuation transportRead ->
                  Cont transportRead provenance replayRead ->
                    Cont replayRead localName budgetRead ->
                      PkgSig bundle budgetRead pkg ->
                        UnaryHistory budgetRead ∧ Cont replayRead localName budgetRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRead pkg ∧
                            hsame budgetRead budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro ledger candidateRoute sourceRoute residualRoute witnessRoute fairnessRoute
    transportRoute replayRoute budgetRoute budgetPkg
  obtain ⟨packet, _dyadicUnary, streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary candidateRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed candidateUnary streamUnary sourceRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed sourceUnary obstructionUnary residualRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed residualUnary dischargeUnary witnessRoute
  have fairnessUnary : UnaryHistory fairnessRead :=
    unary_cont_closed witnessUnary handoffUnary fairnessRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed fairnessUnary continuationUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary provenanceUnary replayRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed replayUnary localNameUnary budgetRoute
  exact
    ⟨budgetUnary, budgetRoute, provenancePkg, budgetPkg, hsame_refl budgetRead⟩

end BEDC.Derived.MetaCICCriticalPathUp
