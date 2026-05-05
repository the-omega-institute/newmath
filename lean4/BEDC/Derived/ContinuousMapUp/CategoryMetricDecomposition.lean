import BEDC.Derived.CategoryUp
import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

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

end BEDC.Derived.ContinuousMapUp
