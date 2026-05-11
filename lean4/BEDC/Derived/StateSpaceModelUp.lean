import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.StateSpaceModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def StateSpaceModelPacket [AskSetup] [PackageSetup]
    (state input output transition inputMap observation trace route provenance hidden
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory output ∧
    UnaryHistory transition ∧ UnaryHistory inputMap ∧ UnaryHistory observation ∧
      UnaryHistory trace ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory hidden ∧ UnaryHistory endpoint ∧ Cont state input trace ∧
          Cont transition inputMap route ∧ Cont trace route provenance ∧
            Cont provenance hidden endpoint ∧ PkgSig bundle endpoint pkg

theorem StateSpaceModelPacket_control_handoff_transport [AskSetup] [PackageSetup]
    {state input output transition inputMap observation trace route provenance hidden endpoint
      state' input' output' transition' inputMap' observation' trace' route' provenance'
      hidden' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StateSpaceModelPacket state input output transition inputMap observation trace route
        provenance hidden endpoint bundle pkg ->
      hsame state state' ->
        hsame input input' ->
          hsame output output' ->
            hsame transition transition' ->
              hsame inputMap inputMap' ->
                hsame observation observation' ->
                  hsame route route' ->
                    hsame hidden hidden' ->
                      Cont state' input' trace' ->
                        Cont transition' inputMap' route' ->
                          Cont trace' route' provenance' ->
                            Cont provenance' hidden' endpoint' ->
                              PkgSig bundle endpoint' pkg ->
                                StateSpaceModelPacket state' input' output' transition'
                                    inputMap' observation' trace' route' provenance' hidden'
                                    endpoint' bundle pkg ∧
                                  hsame trace trace' ∧ hsame provenance provenance' ∧
                                    hsame endpoint endpoint' := by
  intro packet sameState sameInput sameOutput sameTransition sameInputMap sameObservation
    sameRoute sameHidden traceRow' routeRow' provenanceRow' endpointRow' endpointPkg'
  obtain ⟨stateUnary, inputUnary, outputUnary, transitionUnary, inputMapUnary,
    observationUnary, _traceUnary, _routeUnary, _provenanceUnary, hiddenUnary,
    _endpointUnary, traceRow, routeRow, provenanceRow, endpointRow, _endpointPkg⟩ := packet
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have inputUnary' : UnaryHistory input' :=
    unary_transport inputUnary sameInput
  have outputUnary' : UnaryHistory output' :=
    unary_transport outputUnary sameOutput
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have inputMapUnary' : UnaryHistory inputMap' :=
    unary_transport inputMapUnary sameInputMap
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have hiddenUnary' : UnaryHistory hidden' :=
    unary_transport hiddenUnary sameHidden
  have sameTrace : hsame trace trace' :=
    cont_respects_hsame sameState sameInput traceRow traceRow'
  have sameRoute' : hsame route route' :=
    cont_respects_hsame sameTransition sameInputMap routeRow routeRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTrace sameRoute' provenanceRow provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameHidden endpointRow endpointRow'
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed stateUnary' inputUnary' traceRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed transitionUnary' inputMapUnary' routeRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed traceUnary' routeUnary' provenanceRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' hiddenUnary' endpointRow'
  exact
    ⟨⟨stateUnary', inputUnary', outputUnary', transitionUnary', inputMapUnary',
        observationUnary', traceUnary', routeUnary', provenanceUnary', hiddenUnary',
        endpointUnary', traceRow', routeRow', provenanceRow', endpointRow', endpointPkg'⟩,
      sameTrace, sameProvenance, sameEndpoint⟩

end BEDC.Derived.StateSpaceModelUp
