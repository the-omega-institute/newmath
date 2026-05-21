import BEDC.Derived.MetricUp.Transport

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist

def MetricClassifierSpecification (x y d x' y' d' : BHist) : Prop :=
  MetricDistanceWitness x y d ∧ MetricDistanceWitness x' y' d' ∧
    hsame x x' ∧ hsame y y' ∧ hsame d d'

theorem MetricClassifierSpecification_component_transport {x y d x' y' d' : BHist} :
    MetricDistanceWitness x y d -> hsame x x' -> hsame y y' -> hsame d d' ->
      MetricClassifierSpecification x y d x' y' d' ∧ MetricDistanceWitness x' y' d' := by
  intro witness sameX sameY sameD
  have transported : MetricDistanceWitness x' y' d' :=
    MetricDistanceWitness_hsame_fields_transport sameX sameY sameD witness
  exact And.intro
    (And.intro witness
      (And.intro transported
        (And.intro sameX (And.intro sameY sameD))))
    transported

end BEDC.Derived.MetricUp
