import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10CandidateDischargeGate [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead budgetRead socketRead
      dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal budgetRead →
          Cont budgetRead obstruction socketRead →
            Cont socketRead discharge dischargeRead →
              PkgSig bundle dischargeRead pkg →
                UnaryHistory candidateRead ∧ UnaryHistory budgetRead ∧
                  UnaryHistory socketRead ∧ UnaryHistory dischargeRead ∧
                    Cont continuation localName candidateRead ∧
                      Cont candidateRead realSeal budgetRead ∧
                        Cont budgetRead obstruction socketRead ∧
                          Cont socketRead discharge dischargeRead ∧
                            PkgSig bundle realSeal pkg ∧
                              PkgSig bundle dischargeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro ledger candidateRoute budgetRoute socketRoute dischargeRoute dischargePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary candidateRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateUnary realSealUnary budgetRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed budgetUnary obstructionUnary socketRoute
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed socketUnary dischargeUnary dischargeRoute
  exact
    ⟨candidateUnary, budgetUnary, socketUnary, dischargeReadUnary, candidateRoute,
      budgetRoute, socketRoute, dischargeRoute, realSealPkg, dischargePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
