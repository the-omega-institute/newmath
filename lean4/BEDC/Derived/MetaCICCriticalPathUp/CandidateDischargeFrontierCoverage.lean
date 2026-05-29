import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_candidate_discharge_frontier_coverage [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead socketRead dyadicBudget streamBudget regSeqBudget
      realBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      UnaryHistory candidateRead ->
        UnaryHistory dyadicBudget ->
          UnaryHistory regSeqBudget ->
            Cont route candidateRead socketRead ->
              Cont socketRead dyadicBudget streamBudget ->
                Cont streamBudget regSeqBudget realBudget ->
                  PkgSig bundle provenance pkg ->
                    exists coverageRead : BHist,
                      UnaryHistory coverageRead ∧
                        hsame coverageRead (append socketRead realBudget) ∧
                          Cont handoff obstruction dischargeSocket ∧
                            Cont route candidateRead socketRead ∧
                              Cont socketRead dyadicBudget streamBudget ∧
                                Cont streamBudget regSeqBudget realBudget ∧
                                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro packet candidateUnary dyadicUnary regSeqUnary routeCandidateSocket
    socketDyadicStream streamRegSeqReal provenancePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, handoffObstructionSocket,
    _transportLocalName, _packetProvenancePkg⟩ := packet
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed routeUnary candidateUnary routeCandidateSocket
  have streamUnary : UnaryHistory streamBudget :=
    unary_cont_closed socketUnary dyadicUnary socketDyadicStream
  have realUnary : UnaryHistory realBudget :=
    unary_cont_closed streamUnary regSeqUnary streamRegSeqReal
  have coverageUnary : UnaryHistory (append socketRead realBudget) :=
    unary_append_closed socketUnary realUnary
  exact
    Exists.intro (append socketRead realBudget)
      ⟨coverageUnary, hsame_refl (append socketRead realBudget), handoffObstructionSocket,
        routeCandidateSocket, socketDyadicStream, streamRegSeqReal, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
