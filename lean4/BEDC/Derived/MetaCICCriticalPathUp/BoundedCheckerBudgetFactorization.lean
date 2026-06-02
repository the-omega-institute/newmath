import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathBoundedCheckerBudgetFactorization [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead snEndpointRead socketRead
      l10FaceRead checkerRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead strongNorm snEndpointRead →
          Cont discharge realSeal socketRead →
            Cont dyadic stream l10FaceRead →
              Cont handoff continuation checkerRead →
                Cont checkerRead l10FaceRead budgetRead →
                  PkgSig bundle budgetRead pkg →
                    PkgSig bundle l10FaceRead pkg →
                      UnaryHistory candidateRead ∧ UnaryHistory snEndpointRead ∧
                        UnaryHistory socketRead ∧ UnaryHistory l10FaceRead ∧
                          UnaryHistory checkerRead ∧ UnaryHistory budgetRead ∧
                            PkgSig bundle budgetRead pkg ∧
                              PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro ledger continuationLocalNameCandidate candidateStrongNormEndpoint
    dischargeRealSealSocket dyadicStreamL10 handoffContinuationChecker checkerL10Budget
    budgetPkg _l10FacePkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have snEndpointUnary : UnaryHistory snEndpointRead :=
    unary_cont_closed candidateUnary strongNormUnary candidateStrongNormEndpoint
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed dischargeUnary realSealUnary dischargeRealSealSocket
  have l10FaceUnary : UnaryHistory l10FaceRead :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamL10
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed handoffUnary continuationUnary handoffContinuationChecker
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed checkerUnary l10FaceUnary checkerL10Budget
  exact
    ⟨candidateUnary, snEndpointUnary, socketUnary, l10FaceUnary, checkerUnary, budgetUnary,
      budgetPkg, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
