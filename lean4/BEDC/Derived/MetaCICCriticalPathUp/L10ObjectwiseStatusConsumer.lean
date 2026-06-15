import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10ObjectwiseStatusConsumer [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal statusRead closureRead
      objectwiseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName dyadicBudget ->
        Cont dyadicBudget route streamSchedule ->
          Cont streamSchedule normalForm regReadback ->
            Cont regReadback provenance realSeal ->
              Cont realSeal localName statusRead ->
                Cont statusRead provenance closureRead ->
                  Cont closureRead localName objectwiseRead ->
                    PkgSig bundle objectwiseRead pkg ->
                      PkgSig bundle provenance pkg ->
                        UnaryHistory dyadicBudget ∧ UnaryHistory streamSchedule ∧
                          UnaryHistory regReadback ∧ UnaryHistory realSeal ∧
                            UnaryHistory statusRead ∧ UnaryHistory closureRead ∧
                              UnaryHistory objectwiseRead ∧
                                PkgSig bundle objectwiseRead pkg ∧
                                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackProvenanceSeal sealLocalNameStatus statusProvenanceClosure
    closureLocalNameObjectwise objectwisePkg provenancePkgInput
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamScheduleUnary normalFormUnary scheduleNormalFormReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadbackUnary provenanceUnary readbackProvenanceSeal
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed realSealUnary localNameUnary sealLocalNameStatus
  have closureReadUnary : UnaryHistory closureRead :=
    unary_cont_closed statusReadUnary provenanceUnary statusProvenanceClosure
  have objectwiseReadUnary : UnaryHistory objectwiseRead :=
    unary_cont_closed closureReadUnary localNameUnary closureLocalNameObjectwise
  exact
    ⟨dyadicBudgetUnary, streamScheduleUnary, regReadbackUnary, realSealUnary,
      statusReadUnary, closureReadUnary, objectwiseReadUnary, objectwisePkg,
      provenancePkgInput⟩

end BEDC.Derived.MetaCICCriticalPathUp
