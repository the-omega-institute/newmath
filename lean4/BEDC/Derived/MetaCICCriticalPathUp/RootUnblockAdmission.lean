import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRootUnblockAdmission [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName candidateRead ->
        PkgSig bundle candidateRead pkg ->
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
            UnaryHistory realSeal ∧ UnaryHistory candidateRead ∧
              Cont continuation localName candidateRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle candidateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro ledger continuationLocalNameCandidate candidateReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, provenancePkg⟩ := packet
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  exact
    ⟨dyadicUnary, streamUnary, regseqUnary, realSealUnary, candidateReadUnary,
      continuationLocalNameCandidate, provenancePkg, candidateReadPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
