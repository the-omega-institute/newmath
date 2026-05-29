import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateDischargeBudgetRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead budgetRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal budgetRead →
          Cont budgetRead obstruction socketRead →
            PkgSig bundle socketRead pkg →
              UnaryHistory candidateRead ∧ UnaryHistory budgetRead ∧
                UnaryHistory socketRead ∧ Cont continuation localName candidateRead ∧
                  Cont candidateRead realSeal budgetRead ∧
                    Cont budgetRead obstruction socketRead ∧ PkgSig bundle realSeal pkg ∧
                      PkgSig bundle socketRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro ledger candidateRoute budgetRoute socketRoute socketPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary candidateRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateUnary realSealUnary budgetRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed budgetUnary obstructionUnary socketRoute
  exact
    ⟨candidateUnary, budgetUnary, socketUnary, candidateRoute, budgetRoute, socketRoute,
      realSealPkg, socketPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
