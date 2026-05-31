import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateSNReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal readinessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation realSeal readinessRead →
        PkgSig bundle readinessRead pkg →
          UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory handoff ∧
            UnaryHistory discharge ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
              UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory readinessRead ∧
                Cont continuation realSeal readinessRead ∧ PkgSig bundle readinessRead pkg ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro ledger continuationRealSealReadiness readinessPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have readinessUnary : UnaryHistory readinessRead :=
    unary_cont_closed continuationUnary realSealUnary continuationRealSealReadiness
  exact
    ⟨strongNormUnary, normalFormUnary, handoffUnary, dischargeUnary, dyadicUnary,
      streamUnary, regseqUnary, realSealUnary, readinessUnary, continuationRealSealReadiness,
      readinessPkg, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
