import BEDC.Derived.AffineVarUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.Derived.AffineVarUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ProjectiveVarHomogeneousZeroLocusCarrier
    (ChartCarrier : BHist -> Prop) (PolyEvalZero : BHist -> BHist -> Prop)
    (family : ProbeBundle BHist) (projectiveSpace endpoint package : BHist) : Prop :=
  AffineFiniteFamilyZeroLocus ChartCarrier PolyEvalZero family endpoint ∧
    UnaryHistory projectiveSpace ∧ Cont endpoint projectiveSpace package

theorem ProjectiveVarHomogeneousZeroLocusCarrier_bundle_append_exactness
    {ChartCarrier : BHist -> Prop} {PolyEvalZero : BHist -> BHist -> Prop}
    {F G : ProbeBundle BHist} {projectiveSpace endpoint package : BHist} :
    ProjectiveVarHomogeneousZeroLocusCarrier ChartCarrier PolyEvalZero (bundleAppend F G)
        projectiveSpace endpoint package <->
      ProjectiveVarHomogeneousZeroLocusCarrier ChartCarrier PolyEvalZero F projectiveSpace
          endpoint package ∧
        ProjectiveVarHomogeneousZeroLocusCarrier ChartCarrier PolyEvalZero G projectiveSpace
          endpoint package := by
  constructor
  · intro carrier
    have affineParts :
        AffineFiniteFamilyZeroLocus ChartCarrier PolyEvalZero F endpoint ∧
          AffineFiniteFamilyZeroLocus ChartCarrier PolyEvalZero G endpoint :=
      Iff.mp AffineFiniteFamilyZeroLocus_intersection_concat carrier.left
    exact And.intro
      (And.intro affineParts.left (And.intro carrier.right.left carrier.right.right))
      (And.intro affineParts.right (And.intro carrier.right.left carrier.right.right))
  · intro carriers
    have affineAppend :
        AffineFiniteFamilyZeroLocus ChartCarrier PolyEvalZero (bundleAppend F G) endpoint :=
      Iff.mpr AffineFiniteFamilyZeroLocus_intersection_concat
        (And.intro carriers.left.left carriers.right.left)
    exact And.intro affineAppend
      (And.intro carriers.left.right.left carriers.left.right.right)

end BEDC.Derived.ProjectiveVarUp
