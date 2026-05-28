import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPhaseRealStatusProductReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicFace streamFace regSeqRatFace realFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route provenance dyadicFace →
        Cont dyadicFace localName streamFace →
          Cont streamFace normalForm regSeqRatFace →
            Cont regSeqRatFace transport realFace →
              PkgSig bundle realFace pkg →
                UnaryHistory dyadicFace ∧ UnaryHistory streamFace ∧
                  UnaryHistory regSeqRatFace ∧ UnaryHistory realFace ∧
                    Cont route provenance dyadicFace ∧
                      Cont dyadicFace localName streamFace ∧
                        Cont streamFace normalForm regSeqRatFace ∧
                          Cont regSeqRatFace transport realFace ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro packet routeProvenanceDyadic dyadicLocalNameStream streamNormalFormRegSeq
    regSeqTransportReal realPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceDyadic
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed dyadicUnary localNameUnary dyadicLocalNameStream
  have regSeqUnary : UnaryHistory regSeqRatFace :=
    unary_cont_closed streamUnary normalFormUnary streamNormalFormRegSeq
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regSeqUnary transportUnary regSeqTransportReal
  exact
    ⟨dyadicUnary, streamUnary, regSeqUnary, realUnary, routeProvenanceDyadic,
      dyadicLocalNameStream, streamNormalFormRegSeq, regSeqTransportReal, provenancePkg,
      realPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
