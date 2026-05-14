import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricspaceRealDistanceCarrier
    (x y dist radius witness budget classifier provenance realAlg : BHist) : Prop :=
  MetricDistanceWitness x y dist ∧ UnaryHistory radius ∧ Cont dist radius budget ∧
    hsame classifier dist ∧ Cont witness budget provenance ∧ UnaryHistory realAlg

theorem MetricspaceRealDistanceCarrier_public_law_package
    {x y dist radius witness budget classifier provenance realAlg : BHist} :
    MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg ->
      MetricDistanceWitness x y dist ∧ UnaryHistory radius ∧ Cont dist radius budget ∧
        hsame classifier dist ∧ Cont witness budget provenance := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.left⟩

end BEDC.Derived.MetricUp
