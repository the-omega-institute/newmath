import BEDC.Derived.MetricUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.ErrorCodeUp

open BEDC.FKernel.Hist
open BEDC.Derived.MetricUp
open BEDC.Derived.VecSpaceUp

def ErrorCodeMetricCodeword (c : BHist) : Prop :=
  VecSpaceSingletonCarrier c ∧ MetricDistanceWitness c BHist.Empty BHist.Empty

def ErrorCodeMetricReceivedWithinZero (c r : BHist) : Prop :=
  ErrorCodeMetricCodeword c ∧ MetricDistanceWitness c r BHist.Empty

theorem ErrorCodeMetricReceivedWithinZero_unique_decoding_empty {c1 c2 r : BHist} :
    ErrorCodeMetricReceivedWithinZero c1 r ->
      ErrorCodeMetricReceivedWithinZero c2 r ->
        hsame c1 BHist.Empty ∧ hsame c2 BHist.Empty ∧ VecSpaceSingletonClassifier c1 c2 := by
  intro first second
  have firstEndpoints :
      hsame c1 BHist.Empty ∧ hsame r BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := c1) (y := r)).mp first.right
  have secondEndpoints :
      hsame c2 BHist.Empty ∧ hsame r BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := c2) (y := r)).mp second.right
  have sameCodewords : hsame c1 c2 :=
    hsame_trans firstEndpoints.left (hsame_symm secondEndpoints.left)
  exact And.intro firstEndpoints.left
    (And.intro secondEndpoints.left
      (And.intro first.left.left (And.intro second.left.left sameCodewords)))

end BEDC.Derived.ErrorCodeUp
