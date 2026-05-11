import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RiccatiUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RiccatiControlPacket [AskSetup] [PackageSetup]
    (state control cost horizon successor transition predecessor provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory control ∧ UnaryHistory cost ∧ UnaryHistory horizon ∧
    UnaryHistory successor ∧ UnaryHistory transition ∧ UnaryHistory predecessor ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont successor transition predecessor ∧
        Cont predecessor horizon endpoint ∧ PkgSig bundle endpoint pkg

theorem RiccatiControlPacket_finite_ledger_step_closure [AskSetup] [PackageSetup]
    {state control cost horizon successor transition predecessor provenance endpoint state'
      control' cost' horizon' successor' transition' predecessor' provenance' endpoint' :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiccatiControlPacket state control cost horizon successor transition predecessor provenance
        endpoint bundle pkg ->
      hsame state state' ->
        hsame control control' ->
          hsame cost cost' ->
            hsame horizon horizon' ->
              hsame successor successor' ->
                hsame transition transition' ->
                  hsame provenance provenance' ->
                    Cont successor' transition' predecessor' ->
                      Cont predecessor' horizon' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          RiccatiControlPacket state' control' cost' horizon' successor'
                              transition' predecessor' provenance' endpoint' bundle pkg ∧
                            hsame predecessor predecessor' ∧ hsame endpoint endpoint' := by
  intro packet sameState sameControl sameCost sameHorizon sameSuccessor sameTransition
    sameProvenance predecessorRow' endpointRow' endpointPkg'
  obtain ⟨stateUnary, controlUnary, costUnary, horizonUnary, successorUnary,
    transitionUnary, _predecessorUnary, provenanceUnary, _endpointUnary, predecessorRow,
    endpointRow, _endpointPkg⟩ := packet
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have controlUnary' : UnaryHistory control' :=
    unary_transport controlUnary sameControl
  have costUnary' : UnaryHistory cost' :=
    unary_transport costUnary sameCost
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport horizonUnary sameHorizon
  have successorUnary' : UnaryHistory successor' :=
    unary_transport successorUnary sameSuccessor
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have predecessorUnary' : UnaryHistory predecessor' :=
    unary_cont_closed successorUnary' transitionUnary' predecessorRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed predecessorUnary' horizonUnary' endpointRow'
  have samePredecessor : hsame predecessor predecessor' :=
    cont_respects_hsame sameSuccessor sameTransition predecessorRow predecessorRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePredecessor sameHorizon endpointRow endpointRow'
  exact And.intro
    (And.intro stateUnary'
      (And.intro controlUnary'
        (And.intro costUnary'
          (And.intro horizonUnary'
            (And.intro successorUnary'
              (And.intro transitionUnary'
                (And.intro predecessorUnary'
                  (And.intro provenanceUnary'
                    (And.intro endpointUnary'
                      (And.intro predecessorRow'
                        (And.intro endpointRow' endpointPkg')))))))))))
    (And.intro samePredecessor sameEndpoint)

end BEDC.Derived.RiccatiUp
