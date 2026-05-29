import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateDischargeScheduleExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead scheduleRead dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal scheduleRead →
          Cont scheduleRead discharge dischargeRead →
            PkgSig bundle dischargeRead pkg →
              UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧
                UnaryHistory obstruction ∧ UnaryHistory discharge ∧
                  UnaryHistory candidateRead ∧ UnaryHistory scheduleRead ∧
                    UnaryHistory dischargeRead ∧ Cont continuation localName candidateRead ∧
                      Cont candidateRead realSeal scheduleRead ∧
                        Cont scheduleRead discharge dischargeRead ∧
                          PkgSig bundle realSeal pkg ∧ PkgSig bundle dischargeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro ledger candidateRoute scheduleRoute dischargeRoute dischargePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary candidateRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed candidateUnary realSealUnary scheduleRoute
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed scheduleUnary dischargeUnary dischargeRoute
  exact
    ⟨strongNormUnary, normalFormUnary, obstructionUnary, dischargeUnary, candidateUnary,
      scheduleUnary, dischargeReadUnary, candidateRoute, scheduleRoute, dischargeRoute,
      realSealPkg, dischargePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
