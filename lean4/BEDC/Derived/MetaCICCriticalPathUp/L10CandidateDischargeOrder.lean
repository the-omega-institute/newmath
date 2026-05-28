import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10CandidateDischargeOrder [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal normalForm candidateRead →
        PkgSig bundle candidateRead pkg →
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
            UnaryHistory realSeal ∧ UnaryHistory candidateRead ∧
              Cont realSeal normalForm candidateRead ∧
                PkgSig bundle realSeal pkg ∧ PkgSig bundle candidateRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro ledger realSealNormalFormCandidate candidateReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed realSealUnary normalFormUnary realSealNormalFormCandidate
  exact
    ⟨dyadicUnary, streamUnary, regseqUnary, realSealUnary, candidateUnary,
      realSealNormalFormCandidate, realSealPkg, candidateReadPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
