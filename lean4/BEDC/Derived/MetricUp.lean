import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricDistanceWitness (x y dist : BHist) : Prop :=
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory dist ∧ Cont x y dist

theorem MetricDistanceWitness_symmetric_classifier {x y dxy dyx : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y x dyx -> hsame dxy dyx := by
  intro forward reverse
  exact unary_continuation_commutativity forward.1 forward.2.1 forward.2.2.2 reverse.2.2.2

theorem MetricDistanceWitness_prefix_closed {p x y dist : BHist} :
    UnaryHistory p -> MetricDistanceWitness x y dist ->
      MetricDistanceWitness (append p x) y (append p dist) := by
  intro prefixCarrier witness
  cases witness with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro distCarrier distRel =>
              cases distRel
              exact
                And.intro (unary_append_closed prefixCarrier xCarrier)
                  (And.intro yCarrier
                    (And.intro (unary_append_closed prefixCarrier distCarrier)
                      (cont_intro (append_assoc p x y).symm)))

end BEDC.Derived.MetricUp
