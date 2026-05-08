import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DynSystemUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DynSystemFlowPacket [AskSetup] [PackageSetup]
    (phase ode time source target flowWitness endpoint route : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory phase ∧ UnaryHistory ode ∧ UnaryHistory time ∧ UnaryHistory source ∧
    UnaryHistory target ∧ Cont (append phase time) source flowWitness ∧
      Cont flowWitness ode endpoint ∧ Cont endpoint target route ∧ PkgSig bundle route pkg

theorem DynSystemFlowPacket_endpoint_coverage [AskSetup] [PackageSetup]
    {phase ode time source target flowWitness endpoint route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DynSystemFlowPacket phase ode time source target flowWitness endpoint route bundle pkg ->
      UnaryHistory flowWitness ∧ UnaryHistory endpoint ∧ UnaryHistory route ∧
        hsame flowWitness (append (append phase time) source) ∧
          hsame endpoint (append flowWitness ode) ∧ hsame route (append endpoint target) ∧
            PkgSig bundle route pkg := by
  intro packet
  have phaseUnary : UnaryHistory phase := packet.left
  have odeUnary : UnaryHistory ode := packet.right.left
  have timeUnary : UnaryHistory time := packet.right.right.left
  have sourceUnary : UnaryHistory source := packet.right.right.right.left
  have targetUnary : UnaryHistory target := packet.right.right.right.right.left
  have flowWitnessCont : Cont (append phase time) source flowWitness :=
    packet.right.right.right.right.right.left
  have endpointCont : Cont flowWitness ode endpoint :=
    packet.right.right.right.right.right.right.left
  have routeCont : Cont endpoint target route :=
    packet.right.right.right.right.right.right.right.left
  have routePkg : PkgSig bundle route pkg :=
    packet.right.right.right.right.right.right.right.right
  have phaseTimeUnary : UnaryHistory (append phase time) :=
    unary_append_closed phaseUnary timeUnary
  have flowWitnessUnary : UnaryHistory flowWitness :=
    unary_cont_closed phaseTimeUnary sourceUnary flowWitnessCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed flowWitnessUnary odeUnary endpointCont
  have routeUnary : UnaryHistory route :=
    unary_cont_closed endpointUnary targetUnary routeCont
  exact
    And.intro flowWitnessUnary
      (And.intro endpointUnary
        (And.intro routeUnary
          (And.intro flowWitnessCont
            (And.intro endpointCont
              (And.intro routeCont routePkg)))))

end BEDC.Derived.DynSystemUp
