import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNFrontierExtension [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal realRead →
          Cont discharge realRead completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory candidateRead ∧ UnaryHistory realRead ∧
                UnaryHistory completionRead ∧ PkgSig bundle realSeal pkg ∧
                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro ledger continuationLocalCandidate candidateRealRead dischargeRealCompletion
    completionPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalCandidate
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed candidateUnary realSealUnary candidateRealRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed dischargeUnary realReadUnary dischargeRealCompletion
  exact ⟨candidateUnary, realReadUnary, completionUnary, realSealPkg, completionPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
