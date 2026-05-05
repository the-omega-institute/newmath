import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CompactNetTwoStepFactor (center precision extra refined : BHist) : Prop :=
  ∃ net : BHist, CompactNetWitness center precision net ∧
    CompactNetWitness net extra refined

theorem CompactNetTwoStepFactor_composed_closed
    {center precision extra composite refined : BHist} :
    UnaryHistory precision -> UnaryHistory extra -> Cont precision extra composite ->
      CompactNetTwoStepFactor center precision extra refined ->
        CompactNetWitness center composite refined := by
  intro precisionCarrier extraCarrier compositeRel factor
  cases factor with
  | intro net factorData =>
      have prefixed :
          CompactNetWitness (append BHist.Empty center) composite
            (append BHist.Empty refined) :=
        CompactNetWitness_prefixed_composite_closed unary_empty factorData.left
          factorData.right compositeRel
      exact (CompactNetWitness_prefix_iff.mp prefixed).right

theorem CompactNetTwoStepFactor_gluing_package {center precision extra composite net refined :
    BHist} :
    CompactNetWitness center precision net -> CompactNetWitness net extra refined ->
      UnaryHistory precision -> UnaryHistory extra -> Cont precision extra composite ->
        CompactNetTwoStepFactor center precision extra refined ∧
          CompactNetWitness center composite refined := by
  intro first second precisionCarrier extraCarrier compositeRel
  have factor : CompactNetTwoStepFactor center precision extra refined :=
    Exists.intro net (And.intro first second)
  exact And.intro factor
    (CompactNetTwoStepFactor_composed_closed precisionCarrier extraCarrier compositeRel factor)

end BEDC.Derived.CompactUp
