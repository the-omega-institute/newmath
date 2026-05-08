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

theorem DynSystemFlowPacket_identity_flow_obligation [AskSetup] [PackageSetup]
    {state : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory state -> PkgSig bundle state pkg ->
      DynSystemFlowPacket BHist.Empty BHist.Empty BHist.Empty state BHist.Empty state state state
          bundle pkg ∧
        Cont BHist.Empty state state ∧ Cont state BHist.Empty state := by
  intro stateUnary statePkg
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have leftFlow : Cont BHist.Empty state state := cont_left_unit state
  have rightFlow : Cont state BHist.Empty state := cont_right_unit state
  have packet :
      DynSystemFlowPacket BHist.Empty BHist.Empty BHist.Empty state BHist.Empty state state state
          bundle pkg :=
    And.intro emptyUnary
      (And.intro emptyUnary
        (And.intro emptyUnary
          (And.intro stateUnary
            (And.intro emptyUnary
              (And.intro leftFlow
                (And.intro rightFlow
                  (And.intro rightFlow statePkg)))))))
  exact And.intro packet (And.intro leftFlow rightFlow)

theorem DynSystemFlowPacket_flow_route_readback [AskSetup] [PackageSetup]
    {phase ode time source target flowWitness endpoint route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DynSystemFlowPacket phase ode time source target flowWitness endpoint route bundle pkg ->
      hsame flowWitness (append (append phase time) source) ∧
        hsame endpoint (append (append (append phase time) source) ode) ∧
          hsame route (append (append (append (append phase time) source) ode) target) ∧
            PkgSig bundle route pkg := by
  intro packet
  have flowWitnessCont : Cont (append phase time) source flowWitness :=
    packet.right.right.right.right.right.left
  have endpointCont : Cont flowWitness ode endpoint :=
    packet.right.right.right.right.right.right.left
  have routeCont : Cont endpoint target route :=
    packet.right.right.right.right.right.right.right.left
  have routePkg : PkgSig bundle route pkg :=
    packet.right.right.right.right.right.right.right.right
  have endpointReadback : hsame endpoint (append (append (append phase time) source) ode) := by
    cases flowWitnessCont
    exact endpointCont
  have routeReadback :
      hsame route (append (append (append (append phase time) source) ode) target) := by
    cases flowWitnessCont
    cases endpointCont
    exact routeCont
  exact
    And.intro flowWitnessCont
      (And.intro endpointReadback
        (And.intro routeReadback routePkg))

theorem DynSystemFlowPacket_segment_route_exhaustion [AskSetup] [PackageSetup]
    {phase ode time source target flowWitness endpoint route tail finalRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DynSystemFlowPacket phase ode time source target flowWitness endpoint route bundle pkg ->
      UnaryHistory tail -> Cont route tail finalRoute -> PkgSig bundle finalRoute pkg ->
        UnaryHistory flowWitness ∧ UnaryHistory endpoint ∧ UnaryHistory route ∧
          UnaryHistory finalRoute ∧ hsame flowWitness (append (append phase time) source) ∧
            hsame endpoint (append (append (append phase time) source) ode) ∧
              hsame route (append (append (append (append phase time) source) ode) target) ∧
                hsame finalRoute
                  (append (append (append (append (append phase time) source) ode) target)
                    tail) ∧
                  PkgSig bundle finalRoute pkg := by
  intro packet tailUnary finalRouteCont finalRoutePkg
  have endpointRows :=
    DynSystemFlowPacket_endpoint_coverage packet
  have readback :=
    DynSystemFlowPacket_flow_route_readback packet
  have finalRouteUnary : UnaryHistory finalRoute :=
    unary_cont_closed endpointRows.right.right.left tailUnary finalRouteCont
  have finalRouteReadback :
      hsame finalRoute
        (append (append (append (append (append phase time) source) ode) target) tail) := by
    have routeReadback : hsame route
        (append (append (append (append phase time) source) ode) target) :=
      readback.right.right.left
    cases routeReadback
    exact finalRouteCont
  exact And.intro endpointRows.left
    (And.intro endpointRows.right.left
      (And.intro endpointRows.right.right.left
        (And.intro finalRouteUnary
          (And.intro readback.left
            (And.intro readback.right.left
              (And.intro readback.right.right.left
                (And.intro finalRouteReadback finalRoutePkg)))))))

theorem DynSystemFlowPacket_classifier_flow_transport [AskSetup] [PackageSetup]
    {phase phase' ode ode' time time' source source' target target' flowWitness flowWitness'
      endpoint endpoint' route route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DynSystemFlowPacket phase ode time source target flowWitness endpoint route bundle pkg ->
      hsame phase phase' -> hsame ode ode' -> hsame time time' -> hsame source source' ->
        hsame target target' ->
          Cont (append phase' time') source' flowWitness' ->
            Cont flowWitness' ode' endpoint' ->
              Cont endpoint' target' route' ->
                PkgSig bundle route' pkg ->
                  DynSystemFlowPacket phase' ode' time' source' target' flowWitness' endpoint'
                    route' bundle pkg ∧ hsame flowWitness flowWitness' ∧
                    hsame endpoint endpoint' ∧ hsame route route' := by
  intro packet samePhase sameOde sameTime sameSource sameTarget flowWitnessCont'
    endpointCont' routeCont' routePkg'
  have phaseUnary' : UnaryHistory phase' :=
    unary_transport packet.left samePhase
  have odeUnary' : UnaryHistory ode' :=
    unary_transport packet.right.left sameOde
  have timeUnary' : UnaryHistory time' :=
    unary_transport packet.right.right.left sameTime
  have sourceUnary' : UnaryHistory source' :=
    unary_transport packet.right.right.right.left sameSource
  have targetUnary' : UnaryHistory target' :=
    unary_transport packet.right.right.right.right.left sameTarget
  have phaseTimeUnary' : UnaryHistory (append phase' time') :=
    unary_append_closed phaseUnary' timeUnary'
  have flowWitnessUnary' : UnaryHistory flowWitness' :=
    unary_cont_closed phaseTimeUnary' sourceUnary' flowWitnessCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed flowWitnessUnary' odeUnary' endpointCont'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed endpointUnary' targetUnary' routeCont'
  have samePhaseTime : hsame (append phase time) (append phase' time') :=
    cont_respects_hsame samePhase sameTime (rfl : Cont phase time (append phase time))
      (rfl : Cont phase' time' (append phase' time'))
  have sameFlowWitness : hsame flowWitness flowWitness' :=
    cont_respects_hsame samePhaseTime sameSource packet.right.right.right.right.right.left
      flowWitnessCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameFlowWitness sameOde
      packet.right.right.right.right.right.right.left endpointCont'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameEndpoint sameTarget
      packet.right.right.right.right.right.right.right.left routeCont'
  exact
    And.intro
      (And.intro phaseUnary'
        (And.intro odeUnary'
          (And.intro timeUnary'
            (And.intro sourceUnary'
              (And.intro targetUnary'
                (And.intro flowWitnessCont'
                  (And.intro endpointCont'
                    (And.intro routeCont' routePkg'))))))))
      (And.intro sameFlowWitness (And.intro sameEndpoint sameRoute))

theorem DynSystemFlowPacket_endpoint_determinacy_surface [AskSetup] [PackageSetup]
    {phase ode time source target target' flowWitness endpoint endpoint' route route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DynSystemFlowPacket phase ode time source target flowWitness endpoint route bundle pkg ->
      DynSystemFlowPacket phase ode time source target' flowWitness endpoint' route' bundle pkg ->
        hsame target target' -> hsame route route' -> hsame endpoint endpoint' := by
  intro leftPacket rightPacket sameTarget sameRoute
  cases sameTarget
  exact
    cont_common_suffix_cancellation leftPacket.right.right.right.right.right.right.right.left
      rightPacket.right.right.right.right.right.right.right.left sameRoute

theorem DynSystemFlowPacket_composition_flow_obligation [AskSetup] [PackageSetup]
    {phase ode timeA timeB timeAB source middle target flowA endpointA routeA flowB endpointB
      routeB joinedEndpoint joinedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DynSystemFlowPacket phase ode timeA source middle flowA endpointA routeA bundle pkg ->
      DynSystemFlowPacket phase ode timeB middle target flowB endpointB routeB bundle pkg ->
        Cont timeA timeB timeAB ->
          Cont endpointA endpointB joinedEndpoint ->
            Cont joinedEndpoint target joinedRoute ->
              PkgSig bundle joinedRoute pkg ->
                UnaryHistory timeAB ∧ UnaryHistory joinedEndpoint ∧ UnaryHistory joinedRoute ∧
                  hsame timeAB (append timeA timeB) ∧
                    hsame joinedEndpoint (append endpointA endpointB) ∧
                      hsame joinedRoute (append joinedEndpoint target) ∧
                        PkgSig bundle joinedRoute pkg := by
  intro packetA packetB timeABCont joinedEndpointCont joinedRouteCont joinedRoutePkg
  have timeAUnary : UnaryHistory timeA :=
    packetA.right.right.left
  have timeBUnary : UnaryHistory timeB :=
    packetB.right.right.left
  have endpointARows :=
    DynSystemFlowPacket_endpoint_coverage packetA
  have endpointBRows :=
    DynSystemFlowPacket_endpoint_coverage packetB
  have targetUnary : UnaryHistory target :=
    packetB.right.right.right.right.left
  have timeABUnary : UnaryHistory timeAB :=
    unary_cont_closed timeAUnary timeBUnary timeABCont
  have joinedEndpointUnary : UnaryHistory joinedEndpoint :=
    unary_cont_closed endpointARows.right.left endpointBRows.right.left joinedEndpointCont
  have joinedRouteUnary : UnaryHistory joinedRoute :=
    unary_cont_closed joinedEndpointUnary targetUnary joinedRouteCont
  exact And.intro timeABUnary
    (And.intro joinedEndpointUnary
      (And.intro joinedRouteUnary
        (And.intro timeABCont
          (And.intro joinedEndpointCont
            (And.intro joinedRouteCont joinedRoutePkg)))))

end BEDC.Derived.DynSystemUp
