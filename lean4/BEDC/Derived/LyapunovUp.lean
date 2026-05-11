import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LyapunovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LyapunovPacket [AskSetup] [PackageSetup]
    (state transition quadratic positive decrease transports routes provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory quadratic ∧
    UnaryHistory positive ∧ UnaryHistory transports ∧ UnaryHistory provenance ∧
      Cont state transition routes ∧ Cont quadratic positive decrease ∧
        Cont decrease transports endpoint ∧ Cont endpoint provenance name ∧
          PkgSig bundle name pkg

theorem LyapunovPacket_stability_transport [AskSetup] [PackageSetup]
    {state transition quadratic positive decrease transports routes provenance name endpoint state'
      transition' quadratic' positive' decrease' transports' routes' provenance' name'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovPacket state transition quadratic positive decrease transports routes provenance name
        endpoint bundle pkg ->
      hsame state state' ->
        hsame transition transition' ->
          hsame quadratic quadratic' ->
            hsame positive positive' ->
              hsame transports transports' ->
                hsame provenance provenance' ->
                  Cont state' transition' routes' ->
                    Cont quadratic' positive' decrease' ->
                      Cont decrease' transports' endpoint' ->
                        Cont endpoint' provenance' name' ->
                          PkgSig bundle name' pkg ->
                            LyapunovPacket state' transition' quadratic' positive' decrease'
                                transports' routes' provenance' name' endpoint' bundle pkg ∧
                              hsame routes routes' ∧ hsame decrease decrease' ∧
                                hsame endpoint endpoint' ∧ hsame name name' := by
  intro packet sameState sameTransition sameQuadratic samePositive sameTransports sameProvenance
    routesRow' decreaseRow' endpointRow' nameRow' nameSig'
  obtain ⟨stateUnary, transitionUnary, quadraticUnary, positiveUnary, transportsUnary,
    provenanceUnary, routesRow, decreaseRow, endpointRow, nameRow, _nameSig⟩ := packet
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have quadraticUnary' : UnaryHistory quadratic' :=
    unary_transport quadraticUnary sameQuadratic
  have positiveUnary' : UnaryHistory positive' :=
    unary_transport positiveUnary samePositive
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameRoutes : hsame routes routes' :=
    cont_respects_hsame sameState sameTransition routesRow routesRow'
  have decreaseUnary' : UnaryHistory decrease' :=
    unary_cont_closed quadraticUnary' positiveUnary' decreaseRow'
  have sameDecrease : hsame decrease decrease' :=
    cont_respects_hsame sameQuadratic samePositive decreaseRow decreaseRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed decreaseUnary' transportsUnary' endpointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameDecrease sameTransports endpointRow endpointRow'
  have sameName : hsame name name' :=
    cont_respects_hsame sameEndpoint sameProvenance nameRow nameRow'
  have transported :
      LyapunovPacket state' transition' quadratic' positive' decrease' transports' routes'
        provenance' name' endpoint' bundle pkg :=
    ⟨stateUnary', transitionUnary', quadraticUnary', positiveUnary', transportsUnary',
      provenanceUnary', routesRow', decreaseRow', endpointRow', nameRow', nameSig'⟩
  exact ⟨transported, sameRoutes, sameDecrease, sameEndpoint, sameName⟩

end BEDC.Derived.LyapunovUp
