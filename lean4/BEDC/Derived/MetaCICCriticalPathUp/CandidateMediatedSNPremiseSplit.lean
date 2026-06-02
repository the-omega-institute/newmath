import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNPremiseSplit [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead snEndpointRead socketRead
      l10FaceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead strongNorm snEndpointRead →
          Cont discharge realSeal socketRead →
            Cont dyadic stream l10FaceRead →
              PkgSig bundle l10FaceRead pkg →
                UnaryHistory candidateRead ∧ UnaryHistory snEndpointRead ∧
                  UnaryHistory socketRead ∧ UnaryHistory l10FaceRead ∧
                    Cont continuation localName candidateRead ∧
                      Cont candidateRead strongNorm snEndpointRead ∧
                        Cont discharge realSeal socketRead ∧
                          Cont dyadic stream l10FaceRead ∧
                            PkgSig bundle realSeal pkg ∧
                              PkgSig bundle l10FaceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro ledger continuationLocalNameCandidate candidateStrongNormEndpoint
    dischargeRealSealSocket dyadicStreamFace l10FacePkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have endpointUnary : UnaryHistory snEndpointRead :=
    unary_cont_closed candidateUnary strongNormUnary candidateStrongNormEndpoint
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed dischargeUnary realSealUnary dischargeRealSealSocket
  have faceUnary : UnaryHistory l10FaceRead :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamFace
  exact
    ⟨candidateUnary, endpointUnary, socketUnary, faceUnary,
      continuationLocalNameCandidate, candidateStrongNormEndpoint,
      dischargeRealSealSocket, dyadicStreamFace, realSealPkg, l10FacePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
