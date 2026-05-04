import BEDC.Derived.GroupUp.NormalizerAction

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonNormalizerOrbit_action_chain {s x y z : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      GroupSingletonCarrier z -> GroupSingletonNormalizerOrbit x y ->
        GroupSingletonNormalizerOrbit y z ->
          GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
            (append (append s y) BHist.Empty) ∧
          GroupSingletonNormalizerOrbit (append (append s y) BHist.Empty)
            (append (append s z) BHist.Empty) ∧
          GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
            (append (append s z) BHist.Empty) := by
  intro carrierS carrierX carrierY carrierZ orbitXY orbitYZ
  have actedXY :
      GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
        (append (append s y) BHist.Empty) :=
    GroupSingletonNormalizerOrbit_action_invariance carrierS carrierX carrierY orbitXY
  have actedYZ :
      GroupSingletonNormalizerOrbit (append (append s y) BHist.Empty)
        (append (append s z) BHist.Empty) :=
    GroupSingletonNormalizerOrbit_action_invariance carrierS carrierY carrierZ orbitYZ
  have actedXYEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp actedXY
  have actedYZEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp actedYZ
  have actedXZ :
      GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
        (append (append s z) BHist.Empty) :=
    GroupSingletonNormalizerOrbit_coverage_iff.mpr
      (And.intro actedXYEndpoints.left actedYZEndpoints.right)
  exact And.intro actedXY (And.intro actedYZ actedXZ)

theorem GroupSingletonNormalizerOrbit_action_path_iff {s x y z : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      GroupSingletonCarrier z ->
      ((GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
          (append (append s y) BHist.Empty) ∧
        GroupSingletonNormalizerOrbit (append (append s y) BHist.Empty)
          (append (append s z) BHist.Empty)) <->
        (GroupSingletonNormalizerOrbit x y ∧ GroupSingletonNormalizerOrbit y z)) ∧
      (GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
        (append (append s z) BHist.Empty) <-> GroupSingletonNormalizerOrbit x z) := by
  intro carrierS carrierX carrierY carrierZ
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have actedX :
      GroupSingletonCarrier (append (append s x) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierS carrierX)) emptyCarrier)
  have actedY :
      GroupSingletonCarrier (append (append s y) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierS carrierY)) emptyCarrier)
  have actedZ :
      GroupSingletonCarrier (append (append s z) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierS carrierZ)) emptyCarrier)
  have actedXYIff :
      GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
          (append (append s y) BHist.Empty) <->
        GroupSingletonNormalizerOrbit x y := by
    constructor
    · intro orbit
      have _actedEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp orbit
      exact GroupSingletonNormalizerOrbit_coverage_iff.mpr (And.intro carrierX carrierY)
    · intro orbit
      have _baseEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp orbit
      exact GroupSingletonNormalizerOrbit_coverage_iff.mpr (And.intro actedX actedY)
  have actedYZIff :
      GroupSingletonNormalizerOrbit (append (append s y) BHist.Empty)
          (append (append s z) BHist.Empty) <->
        GroupSingletonNormalizerOrbit y z := by
    constructor
    · intro orbit
      have _actedEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp orbit
      exact GroupSingletonNormalizerOrbit_coverage_iff.mpr (And.intro carrierY carrierZ)
    · intro orbit
      have _baseEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp orbit
      exact GroupSingletonNormalizerOrbit_coverage_iff.mpr (And.intro actedY actedZ)
  have actedXZIff :
      GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
          (append (append s z) BHist.Empty) <->
        GroupSingletonNormalizerOrbit x z := by
    constructor
    · intro orbit
      have _actedEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp orbit
      exact GroupSingletonNormalizerOrbit_coverage_iff.mpr (And.intro carrierX carrierZ)
    · intro orbit
      have _baseEndpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp orbit
      exact GroupSingletonNormalizerOrbit_coverage_iff.mpr (And.intro actedX actedZ)
  constructor
  · constructor
    · intro actedPath
      exact And.intro (actedXYIff.mp actedPath.left) (actedYZIff.mp actedPath.right)
    · intro basePath
      exact And.intro (actedXYIff.mpr basePath.left) (actedYZIff.mpr basePath.right)
  · exact actedXZIff

end BEDC.Derived.GroupUp
