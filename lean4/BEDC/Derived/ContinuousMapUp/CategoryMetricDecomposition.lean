import BEDC.Derived.CategoryUp
import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

def ContinuousMapMetricSourceSpec (source map target modulus cert distance : BHist) : Prop :=
  CategoryHomCarrier source target map ∧ ContinuousModulusWitness target modulus cert ∧
    MetricDistanceWitness source target distance

theorem ContinuousMapCarrier_category_metric_decomposition
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ↔
      CategoryHomCarrier source target map ∧
        ContinuousModulusWitness target modulus cert ∧
          MetricDistanceWitness source target distance ∧ Cont source map target ∧
            Cont target modulus cert ∧ Cont source target distance := by
  constructor
  · intro carrier
    have functionCarrier := carrier.left
    have graphRel : Cont source map target :=
      functionCarrier.right.right.right.right.left
    have certRel : Cont target modulus cert :=
      functionCarrier.right.right.right.right.right
    have distanceRel : Cont source target distance :=
      carrier.right.right.right.right
    have homCarrier : CategoryHomCarrier source target map :=
      And.intro functionCarrier.left
        (And.intro functionCarrier.right.left
          (And.intro functionCarrier.right.right.left graphRel))
    have modulusWitness : ContinuousModulusWitness target modulus cert :=
      And.intro functionCarrier.right.left
        (And.intro functionCarrier.right.right.right.left
          (And.intro
            (unary_cont_closed functionCarrier.right.left functionCarrier.right.right.right.left
              certRel)
            certRel))
    exact
      And.intro homCarrier
        (And.intro modulusWitness
          (And.intro carrier.right
            (And.intro graphRel (And.intro certRel distanceRel))))
  · intro data
    have homCarrier := data.left
    have modulusWitness := data.right.left
    have distanceWitness := data.right.right.left
    have graphRel : Cont source map target := data.right.right.right.left
    have certRel : Cont target modulus cert := data.right.right.right.right.left
    have functionCarrier : ContinuousFunctionCarrier source map target modulus cert :=
      And.intro homCarrier.left
        (And.intro homCarrier.right.left
          (And.intro homCarrier.right.right.left
            (And.intro modulusWitness.right.left (And.intro graphRel certRel))))
    exact And.intro functionCarrier distanceWitness

theorem ContinuousMapMetricSourceSpec_canonical_carrier {source map target modulus cert : BHist} :
    ContinuousMapMetricSourceSpec source map target modulus cert (append source target) ->
      ContinuousMapCarrier source map target modulus cert (append source target) := by
  intro sourceSpec
  have graphRel : Cont source map target := sourceSpec.left.right.right.right
  have certRel : Cont target modulus cert := sourceSpec.right.left.right.right.right
  have distanceRel : Cont source target (append source target) :=
    sourceSpec.right.right.right.right.right
  exact ContinuousMapCarrier_category_metric_decomposition.mpr
    (And.intro sourceSpec.left
      (And.intro sourceSpec.right.left
        (And.intro sourceSpec.right.right
          (And.intro graphRel (And.intro certRel distanceRel)))))

theorem ContinuousMapCarrier_categorical_canonical_distance_exactness
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ↔
      CategoryHomCarrier source target map ∧ ContinuousModulusWitness target modulus cert ∧
        hsame distance (append source target) := by
  constructor
  · intro carrier
    have decomposed := ContinuousMapCarrier_category_metric_decomposition.mp carrier
    have exactDistance := ContinuousMapCarrier_canonical_distance_exactness.mp carrier
    exact And.intro decomposed.left
      (And.intro decomposed.right.left exactDistance.right)
  · intro data
    have homCarrier := data.left
    have modulusWitness := data.right.left
    have functionCarrier : ContinuousFunctionCarrier source map target modulus cert :=
      And.intro homCarrier.left
        (And.intro homCarrier.right.left
          (And.intro homCarrier.right.right.left
            (And.intro modulusWitness.right.left
              (And.intro homCarrier.right.right.right modulusWitness.right.right.right))))
    exact ContinuousMapCarrier_canonical_distance_exactness.mpr
      (And.intro functionCarrier data.right.right)

theorem ContinuousMapCarrier_prefixed_categorical_canonical_distance_exactness
    {p source map target modulus cert distance displayed : BHist} :
    UnaryHistory p -> CategoryHomCarrier source target map ->
      ContinuousModulusWitness target modulus cert -> hsame distance (append source target) ->
        (ContinuousMapCarrier (append p source) map (append p target) modulus
          (append p cert) displayed ↔
            hsame displayed (append (append p source) (append p target))) := by
  intro prefixCarrier homCarrier modulusWitness sameDistance
  have baseCarrier :
      ContinuousMapCarrier source map target modulus cert distance :=
    ContinuousMapCarrier_categorical_canonical_distance_exactness.mpr
      (And.intro homCarrier (And.intro modulusWitness sameDistance))
  exact ContinuousMapCarrier_prefix_canonical_distance_exactness prefixCarrier baseCarrier

end BEDC.Derived.ContinuousMapUp
