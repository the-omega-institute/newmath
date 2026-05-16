import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatStreamNameDyadicRealHandoffExactness [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback stream dyadic realSeal terminal
      endpoint' regularity' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback bundle pkg ->
      UnaryHistory stream ->
        UnaryHistory dyadic ->
          UnaryHistory realSeal ->
            Cont stream dyadic schedule ->
              hsame endpoint endpoint' ->
                Cont endpoint' radius regularity' ->
                  Cont regularity' provenance readback' ->
                    Cont provenance realSeal terminal ->
                      PkgSig bundle readback' pkg ->
                        RegSeqRatStreamCarrier schedule index endpoint' radius regularity'
                            provenance readback' bundle pkg ∧
                          UnaryHistory schedule ∧ UnaryHistory terminal ∧
                            hsame readback readback' ∧ Cont stream dyadic schedule ∧
                              Cont provenance realSeal terminal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier streamUnary dyadicUnary realSealUnary streamDyadicSchedule
    sameEndpoint targetRegularity targetReadback provenanceRealSealTerminal pkgReadback'
  have handoff :
      RegSeqRatStreamCarrier schedule index endpoint' radius regularity' provenance readback'
          bundle pkg ∧
        hsame regularity regularity' ∧ hsame readback readback' :=
    RegSeqRatStreamCarrier_real_seal_handoff carrier sameEndpoint targetRegularity
      targetReadback pkgReadback'
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicSchedule
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed carrier.right.right.right.right.right.left realSealUnary
      provenanceRealSealTerminal
  exact
    ⟨handoff.left, scheduleUnary, terminalUnary, handoff.right.right, streamDyadicSchedule,
      provenanceRealSealTerminal⟩

end BEDC.Derived.RegSeqRatUp
