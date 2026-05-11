import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LQRUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LQRFiniteControlCarrier
    (state control transition cost horizon estimator backward provenance endpoint : BHist) : Prop :=
  UnaryHistory state ∧ UnaryHistory control ∧ UnaryHistory cost ∧ UnaryHistory horizon ∧
    UnaryHistory estimator ∧ Cont state control transition ∧ Cont transition cost backward ∧
      Cont backward estimator provenance ∧ Cont provenance horizon endpoint

theorem LQRFiniteControlCarrier_transition_stability
    {state control transition cost horizon estimator backward provenance endpoint state' control'
      transition' cost' horizon' estimator' backward' provenance' endpoint' : BHist} :
    LQRFiniteControlCarrier state control transition cost horizon estimator backward provenance
        endpoint ->
      hsame state state' ->
        hsame control control' ->
          hsame cost cost' ->
            hsame horizon horizon' ->
              hsame estimator estimator' ->
                Cont state' control' transition' ->
                  Cont transition' cost' backward' ->
                    Cont backward' estimator' provenance' ->
                      Cont provenance' horizon' endpoint' ->
                        LQRFiniteControlCarrier state' control' transition' cost' horizon'
                            estimator' backward' provenance' endpoint' ∧
                          hsame transition transition' ∧
                            hsame backward backward' ∧
                              hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameState sameControl sameCost sameHorizon sameEstimator transitionRow'
    backwardRow' provenanceRow' endpointRow'
  rcases carrier with
    ⟨stateUnary, controlUnary, costUnary, horizonUnary, estimatorUnary, transitionRow,
      backwardRow, provenanceRow, endpointRow⟩
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have controlUnary' : UnaryHistory control' :=
    unary_transport controlUnary sameControl
  have costUnary' : UnaryHistory cost' :=
    unary_transport costUnary sameCost
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport horizonUnary sameHorizon
  have estimatorUnary' : UnaryHistory estimator' :=
    unary_transport estimatorUnary sameEstimator
  have sameTransition : hsame transition transition' :=
    cont_respects_hsame sameState sameControl transitionRow transitionRow'
  have sameBackward : hsame backward backward' :=
    cont_respects_hsame sameTransition sameCost backwardRow backwardRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameBackward sameEstimator provenanceRow provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameHorizon endpointRow endpointRow'
  exact And.intro
    (And.intro stateUnary'
      (And.intro controlUnary'
        (And.intro costUnary'
          (And.intro horizonUnary'
            (And.intro estimatorUnary'
              (And.intro transitionRow'
                (And.intro backwardRow' (And.intro provenanceRow' endpointRow'))))))))
    (And.intro sameTransition
      (And.intro sameBackward (And.intro sameProvenance sameEndpoint)))

def LQRFiniteControlPacket [AskSetup] [PackageSetup]
    (state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧
    UnaryHistory control ∧
      UnaryHistory transition ∧
        UnaryHistory cost ∧
          UnaryHistory horizon ∧
            UnaryHistory successorValue ∧
              UnaryHistory estimatorInput ∧
                UnaryHistory backwardUpdate ∧
                  UnaryHistory predecessorValue ∧
                    UnaryHistory endpoint ∧
                      Cont state control transition ∧
                        Cont transition cost successorValue ∧
                          Cont successorValue estimatorInput backwardUpdate ∧
                            Cont backwardUpdate horizon predecessorValue ∧
                              Cont predecessorValue cost endpoint ∧
                                Cont estimatorInput transition backwardUpdate ∧
                                  Cont backwardUpdate control predecessorValue ∧
                                    Cont successorValue horizon endpoint ∧ PkgSig bundle endpoint pkg

theorem LQRFiniteControlPacket_namecert_seed_obligation_surface [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
      backwardUpdate predecessorValue endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              LQRFiniteControlPacket state control transition cost horizon successorValue
                estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              LQRFiniteControlPacket state control transition cost horizon successorValue
                estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              LQRFiniteControlPacket state control transition cost horizon successorValue
                estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont successorValue estimatorInput backwardUpdate ∧
          Cont backwardUpdate horizon predecessorValue ∧ PkgSig bundle endpoint pkg := by
  intro packet
  let Carrier : BHist -> Prop :=
    fun row : BHist =>
      exists e : BHist,
        LQRFiniteControlPacket state control transition cost horizon successorValue
          estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e
  have endpointCarrier : Carrier endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointCarrier
      equiv_refl := by
        intro row _rowCarrier
        exact hsame_refl row
      equiv_symm := by
        intro row other rowOther
        exact hsame_symm rowOther
      equiv_trans := by
        intro row middle other rowMiddle middleOther
        exact hsame_trans rowMiddle middleOther
      carrier_respects_equiv := by
        intro row other rowOther rowCarrier
        cases rowCarrier with
        | intro e rowWitness =>
            exact Exists.intro e
              (And.intro rowWitness.left (hsame_trans (hsame_symm rowOther) rowWitness.right))
    }
    pattern_sound := by
      intro _row rowCarrier
      exact rowCarrier
    ledger_sound := by
      intro _row rowCarrier
      exact rowCarrier
  }
  rcases packet with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, backwardCont, predecessorCont, _, _, _, _, pkgRow⟩
  exact And.intro cert (And.intro backwardCont (And.intro predecessorCont pkgRow))

theorem LQRFiniteControlPacket_dynamic_programming_row [AskSetup] [PackageSetup]
    {state control transition cost horizon estimator successor update predecessor endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon estimator successor update
      predecessor endpoint bundle pkg ->
        Cont successor transition update ∧ Cont update control predecessor ∧
          Cont predecessor cost endpoint ∧ Cont estimator horizon endpoint ∧
            UnaryHistory horizon ∧ PkgSig bundle endpoint pkg := by
  intro packet
  rcases packet with
    ⟨_, _, _, _, horizonUnary, _, _, _, _, _, _, _, _, _, predecessorEndpoint,
      successorUpdate, updatePredecessor, estimatorEndpoint, endpointPkg⟩
  exact And.intro successorUpdate
    (And.intro updatePredecessor
      (And.intro predecessorEndpoint
        (And.intro estimatorEndpoint (And.intro horizonUnary endpointPkg))))

theorem LQRFiniteControlCarrier_transition_transport
    {state control transition cost horizon estimator backward provenance endpoint state' control'
      transition' cost' horizon' estimator' backward' provenance' endpoint' : BHist} :
    LQRFiniteControlCarrier state control transition cost horizon estimator backward provenance
        endpoint ->
      hsame state state' ->
        hsame control control' ->
          hsame cost cost' ->
            hsame horizon horizon' ->
              hsame estimator estimator' ->
                Cont state' control' transition' ->
                  Cont transition' cost' backward' ->
                    Cont backward' estimator' provenance' ->
                      Cont provenance' horizon' endpoint' ->
                        LQRFiniteControlCarrier state' control' transition' cost' horizon'
                            estimator' backward' provenance' endpoint' ∧
                          hsame transition transition' ∧
                            hsame backward backward' ∧ hsame provenance provenance' ∧
                              hsame endpoint endpoint' := by
  intro carrier sameState sameControl sameCost sameHorizon sameEstimator transitionRow'
    backwardRow' provenanceRow' endpointRow'
  have stateUnary' : UnaryHistory state' :=
    unary_transport carrier.left sameState
  have controlUnary' : UnaryHistory control' :=
    unary_transport carrier.right.left sameControl
  have costUnary' : UnaryHistory cost' :=
    unary_transport carrier.right.right.left sameCost
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport carrier.right.right.right.left sameHorizon
  have estimatorUnary' : UnaryHistory estimator' :=
    unary_transport carrier.right.right.right.right.left sameEstimator
  have sameTransition : hsame transition transition' :=
    cont_respects_hsame sameState sameControl carrier.right.right.right.right.right.left
      transitionRow'
  have sameBackward : hsame backward backward' :=
    cont_respects_hsame sameTransition sameCost
      carrier.right.right.right.right.right.right.left backwardRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameBackward sameEstimator
      carrier.right.right.right.right.right.right.right.left provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameHorizon
      carrier.right.right.right.right.right.right.right.right endpointRow'
  have carrier' :
      LQRFiniteControlCarrier state' control' transition' cost' horizon' estimator' backward'
        provenance' endpoint' :=
    And.intro stateUnary'
      (And.intro controlUnary'
        (And.intro costUnary'
          (And.intro horizonUnary'
            (And.intro estimatorUnary'
              (And.intro transitionRow'
                (And.intro backwardRow' (And.intro provenanceRow' endpointRow')))))))
  exact And.intro carrier'
    (And.intro sameTransition
      (And.intro sameBackward (And.intro sameProvenance sameEndpoint)))

theorem LQRFiniteControlPacket_finite_horizon_riccati_transport [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint state' control' transition' cost' horizon' successorValue'
      estimatorInput' backwardUpdate' predecessorValue' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
      backwardUpdate predecessorValue endpoint bundle pkg ->
      LQRFiniteControlPacket state' control' transition' cost' horizon' successorValue'
        estimatorInput' backwardUpdate' predecessorValue' endpoint' bundle pkg ->
      hsame successorValue successorValue' ->
      hsame estimatorInput estimatorInput' ->
      hsame horizon horizon' ->
      hsame cost cost' ->
      hsame backwardUpdate backwardUpdate' ∧ hsame predecessorValue predecessorValue' ∧
        hsame endpoint endpoint' := by
  intro packet packet' sameSuccessor sameEstimator sameHorizon sameCost
  rcases packet with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, backwardRow, predecessorRow, endpointRow, _, _, _, _⟩
  rcases packet' with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, backwardRow', predecessorRow', endpointRow', _, _, _, _⟩
  have sameBackward : hsame backwardUpdate backwardUpdate' :=
    cont_respects_hsame sameSuccessor sameEstimator backwardRow backwardRow'
  have samePredecessor : hsame predecessorValue predecessorValue' :=
    cont_respects_hsame sameBackward sameHorizon predecessorRow predecessorRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePredecessor sameCost endpointRow endpointRow'
  exact And.intro sameBackward (And.intro samePredecessor sameEndpoint)

theorem LQR_dynamic_programming_cont_determinacy
    {successor successor' transition transition' control control' cost cost' estimator estimator'
      provenance provenance' st st' stc stc' stcc stcc' stcce stcce' predecessor
      predecessor' : BHist} :
    hsame successor successor' -> hsame transition transition' -> hsame control control' ->
      hsame cost cost' -> hsame estimator estimator' -> hsame provenance provenance' ->
        Cont successor transition st -> Cont successor' transition' st' ->
          Cont st control stc -> Cont st' control' stc' ->
            Cont stc cost stcc -> Cont stc' cost' stcc' ->
              Cont stcc estimator stcce -> Cont stcc' estimator' stcce' ->
                Cont stcce provenance predecessor ->
                  Cont stcce' provenance' predecessor' -> hsame predecessor predecessor' := by
  intro sameSuccessor sameTransition sameControl sameCost sameEstimator sameProvenance rowSt rowSt'
    rowStc rowStc' rowStcc rowStcc' rowStcce rowStcce' rowPredecessor rowPredecessor'
  have sameSt : hsame st st' :=
    cont_respects_hsame sameSuccessor sameTransition rowSt rowSt'
  have sameStc : hsame stc stc' :=
    cont_respects_hsame sameSt sameControl rowStc rowStc'
  have sameStcc : hsame stcc stcc' :=
    cont_respects_hsame sameStc sameCost rowStcc rowStcc'
  have sameStcce : hsame stcce stcce' :=
    cont_respects_hsame sameStcc sameEstimator rowStcce rowStcce'
  exact cont_respects_hsame sameStcce sameProvenance rowPredecessor rowPredecessor'

theorem LQRFiniteControlPacket_transition_stability [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint state' control' transition' cost' horizon' successorValue'
      estimatorInput' backwardUpdate' predecessorValue' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      hsame state state' ->
        hsame control control' ->
          hsame cost cost' ->
            hsame horizon horizon' ->
              hsame estimatorInput estimatorInput' ->
                Cont state' control' transition' ->
                  Cont transition' cost' successorValue' ->
                    Cont successorValue' estimatorInput' backwardUpdate' ->
                      Cont backwardUpdate' horizon' predecessorValue' ->
                        Cont predecessorValue' cost' endpoint' ->
                          Cont estimatorInput' transition' backwardUpdate' ->
                            Cont backwardUpdate' control' predecessorValue' ->
                              Cont successorValue' horizon' endpoint' ->
                                PkgSig bundle endpoint' pkg ->
                                  LQRFiniteControlPacket state' control' transition' cost' horizon'
                                      successorValue' estimatorInput' backwardUpdate'
                                      predecessorValue' endpoint' bundle pkg ∧
                                    hsame transition transition' ∧
                                      hsame successorValue successorValue' ∧
                                        hsame backwardUpdate backwardUpdate' ∧
                                          hsame predecessorValue predecessorValue' ∧
                                            hsame endpoint endpoint' := by
  intro packet sameState sameControl sameCost sameHorizon sameEstimator rowTransition'
    rowSuccessor' rowBackward' rowPredecessor' rowEndpoint' rowEstimatorBackward'
    rowControlPredecessor' rowHorizonEndpoint' pkgSig'
  rcases packet with
    ⟨stateUnary, controlUnary, transitionUnary, costUnary, horizonUnary, successorUnary,
      estimatorUnary, backwardUnary, predecessorUnary, endpointUnary, rowTransition,
      rowSuccessor, rowBackward, rowPredecessor, rowEndpoint, rowEstimatorBackward,
      rowControlPredecessor, rowHorizonEndpoint, _pkgSig⟩
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have controlUnary' : UnaryHistory control' :=
    unary_transport controlUnary sameControl
  have costUnary' : UnaryHistory cost' :=
    unary_transport costUnary sameCost
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport horizonUnary sameHorizon
  have estimatorUnary' : UnaryHistory estimatorInput' :=
    unary_transport estimatorUnary sameEstimator
  have sameTransition : hsame transition transition' :=
    cont_respects_hsame sameState sameControl rowTransition rowTransition'
  have sameSuccessor : hsame successorValue successorValue' :=
    cont_respects_hsame sameTransition sameCost rowSuccessor rowSuccessor'
  have sameBackward : hsame backwardUpdate backwardUpdate' :=
    cont_respects_hsame sameSuccessor sameEstimator rowBackward rowBackward'
  have samePredecessor : hsame predecessorValue predecessorValue' :=
    cont_respects_hsame sameBackward sameHorizon rowPredecessor rowPredecessor'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePredecessor sameCost rowEndpoint rowEndpoint'
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have successorUnary' : UnaryHistory successorValue' :=
    unary_transport successorUnary sameSuccessor
  have backwardUnary' : UnaryHistory backwardUpdate' :=
    unary_transport backwardUnary sameBackward
  have predecessorUnary' : UnaryHistory predecessorValue' :=
    unary_transport predecessorUnary samePredecessor
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have packet' :
      LQRFiniteControlPacket state' control' transition' cost' horizon' successorValue'
        estimatorInput' backwardUpdate' predecessorValue' endpoint' bundle pkg :=
    by
      constructor
      · exact stateUnary'
      constructor
      · exact controlUnary'
      constructor
      · exact transitionUnary'
      constructor
      · exact costUnary'
      constructor
      · exact horizonUnary'
      constructor
      · exact successorUnary'
      constructor
      · exact estimatorUnary'
      constructor
      · exact backwardUnary'
      constructor
      · exact predecessorUnary'
      constructor
      · exact endpointUnary'
      constructor
      · exact rowTransition'
      constructor
      · exact rowSuccessor'
      constructor
      · exact rowBackward'
      constructor
      · exact rowPredecessor'
      constructor
      · exact rowEndpoint'
      constructor
      · exact rowEstimatorBackward'
      constructor
      · exact rowControlPredecessor'
      constructor
      · exact rowHorizonEndpoint'
      exact pkgSig'
  exact And.intro packet'
    (And.intro sameTransition
      (And.intro sameSuccessor
        (And.intro sameBackward (And.intro samePredecessor sameEndpoint))))

theorem LQRFiniteControlPacket_transition_transport [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint state' control' transition' cost' horizon' successorValue'
      estimatorInput' backwardUpdate' predecessorValue' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      hsame state state' ->
        hsame control control' ->
          hsame transition transition' ->
            hsame cost cost' ->
              hsame horizon horizon' ->
                hsame successorValue successorValue' ->
                  hsame estimatorInput estimatorInput' ->
                    Cont state' control' transition' ->
                      Cont transition' cost' successorValue' ->
                        Cont successorValue' estimatorInput' backwardUpdate' ->
                          Cont backwardUpdate' horizon' predecessorValue' ->
                            Cont predecessorValue' cost' endpoint' ->
                              Cont estimatorInput' transition' backwardUpdate' ->
                                Cont backwardUpdate' control' predecessorValue' ->
                                  Cont successorValue' horizon' endpoint' ->
                                    PkgSig bundle endpoint' pkg ->
                                      LQRFiniteControlPacket state' control' transition' cost'
                                          horizon' successorValue' estimatorInput' backwardUpdate'
                                          predecessorValue' endpoint' bundle pkg ∧
                                        hsame backwardUpdate backwardUpdate' ∧
                                          hsame predecessorValue predecessorValue' ∧
                                            hsame endpoint endpoint' := by
  intro packet sameState sameControl sameTransition sameCost sameHorizon sameSuccessor
    sameEstimator stateControlTransition transitionCostSuccessor successorEstimatorBackward
    backwardHorizonPredecessor predecessorCostEndpoint estimatorTransitionBackward
    backwardControlPredecessor successorHorizonEndpoint endpointPkg
  rcases packet with
    ⟨stateUnary, controlUnary, transitionUnary, costUnary, horizonUnary, successorUnary,
      estimatorUnary, _backwardUnary, _predecessorUnary, _endpointUnary, _stateControl,
      _transitionCost, successorEstimator, backwardHorizon, predecessorCost,
      estimatorTransition, _backwardControl, _successorHorizon, _pkgRow⟩
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have controlUnary' : UnaryHistory control' :=
    unary_transport controlUnary sameControl
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have costUnary' : UnaryHistory cost' :=
    unary_transport costUnary sameCost
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport horizonUnary sameHorizon
  have successorUnary' : UnaryHistory successorValue' :=
    unary_transport successorUnary sameSuccessor
  have estimatorUnary' : UnaryHistory estimatorInput' :=
    unary_transport estimatorUnary sameEstimator
  have backwardUnary' : UnaryHistory backwardUpdate' :=
    unary_cont_closed successorUnary' estimatorUnary' successorEstimatorBackward
  have predecessorUnary' : UnaryHistory predecessorValue' :=
    unary_cont_closed backwardUnary' horizonUnary' backwardHorizonPredecessor
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed predecessorUnary' costUnary' predecessorCostEndpoint
  have sameBackward : hsame backwardUpdate backwardUpdate' :=
    cont_respects_hsame sameSuccessor sameEstimator successorEstimator successorEstimatorBackward
  have samePredecessor : hsame predecessorValue predecessorValue' :=
    cont_respects_hsame sameBackward sameHorizon backwardHorizon backwardHorizonPredecessor
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePredecessor sameCost predecessorCost predecessorCostEndpoint
  exact
    ⟨⟨stateUnary', controlUnary', transitionUnary', costUnary', horizonUnary', successorUnary',
        estimatorUnary', backwardUnary', predecessorUnary', endpointUnary', stateControlTransition,
        transitionCostSuccessor, successorEstimatorBackward, backwardHorizonPredecessor,
        predecessorCostEndpoint, estimatorTransitionBackward, backwardControlPredecessor,
        successorHorizonEndpoint, endpointPkg⟩,
      sameBackward, samePredecessor, sameEndpoint⟩

theorem LQRFiniteControlPacket_estimator_control_consumption_boundary [AskSetup]
    [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint successorValue' estimatorInput' transition' control' cost'
      backwardUpdate' predecessorValue' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      hsame successorValue successorValue' ->
        hsame estimatorInput estimatorInput' ->
          hsame transition transition' ->
            hsame control control' ->
              hsame cost cost' ->
                Cont estimatorInput' transition' backwardUpdate' ->
                  Cont backwardUpdate' control' predecessorValue' ->
                    Cont predecessorValue' cost' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        hsame backwardUpdate backwardUpdate' ∧
                          hsame predecessorValue predecessorValue' ∧
                            hsame endpoint endpoint' := by
  intro packet _sameSuccessor sameEstimator sameTransition sameControl sameCost
    estimatorTransitionRow' backwardControlRow' predecessorCostRow' _endpointPkg'
  rcases packet with
    ⟨_stateUnary, _controlUnary, _transitionUnary, _costUnary, _horizonUnary,
      _successorUnary, _estimatorUnary, _backwardUnary, _predecessorUnary, _endpointUnary,
      _stateControlRow, _transitionCostRow, _successorEstimatorRow, _backwardHorizonRow,
      predecessorCostRow, estimatorTransitionRow, backwardControlRow, _successorHorizonRow,
      _endpointPkg⟩
  have sameBackward : hsame backwardUpdate backwardUpdate' :=
    cont_respects_hsame sameEstimator sameTransition estimatorTransitionRow estimatorTransitionRow'
  have samePredecessor : hsame predecessorValue predecessorValue' :=
    cont_respects_hsame sameBackward sameControl backwardControlRow backwardControlRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePredecessor sameCost predecessorCostRow predecessorCostRow'
  exact And.intro sameBackward (And.intro samePredecessor sameEndpoint)

theorem LQRFiniteControlPacket_quadratic_cost_transport_exactness [AskSetup]
    [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint transition' cost' successorValue' predecessorValue' endpoint' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      hsame transition transition' ->
        hsame cost cost' ->
          hsame predecessorValue predecessorValue' ->
            Cont transition' cost' successorValue' ->
              Cont predecessorValue' cost' endpoint' ->
                hsame successorValue successorValue' ∧ hsame endpoint endpoint' := by
  intro packet sameTransition sameCost samePredecessor transitionCostRow' predecessorCostRow'
  rcases packet with
    ⟨_stateUnary, _controlUnary, _transitionUnary, _costUnary, _horizonUnary,
      _successorUnary, _estimatorUnary, _backwardUnary, _predecessorUnary, _endpointUnary,
      _stateControlRow, transitionCostRow, _successorEstimatorRow, _backwardHorizonRow,
      predecessorCostRow, _estimatorTransitionRow, _backwardControlRow, _successorHorizonRow,
      _endpointPkg⟩
  have sameSuccessor : hsame successorValue successorValue' :=
    cont_respects_hsame sameTransition sameCost transitionCostRow transitionCostRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePredecessor sameCost predecessorCostRow predecessorCostRow'
  exact And.intro sameSuccessor sameEndpoint

end BEDC.Derived.LQRUp
