import BEDC.Derived.MetaCICCriticalPathUp.CandidateMediatedSNFrontier

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNSocketInductionFrontier [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier socket inductionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName frontier ->
        Cont unblock obstruction socket ->
          Cont frontier socket inductionRead ->
            PkgSig bundle inductionRead pkg ->
              UnaryHistory frontier ∧ UnaryHistory socket ∧ UnaryHistory inductionRead ∧
                PkgSig bundle realSeal pkg ∧ PkgSig bundle inductionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro ledger continuationLocalFrontier unblockObstructionSocket frontierSocketInduction
    inductionPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have socketUnary : UnaryHistory socket :=
    unary_cont_closed unblockUnary obstructionUnary unblockObstructionSocket
  have inductionUnary : UnaryHistory inductionRead :=
    unary_cont_closed frontierUnary socketUnary frontierSocketInduction
  exact ⟨frontierUnary, socketUnary, inductionUnary, realSealPkg, inductionPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
