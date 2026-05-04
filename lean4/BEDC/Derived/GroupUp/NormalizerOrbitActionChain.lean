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

end BEDC.Derived.GroupUp
