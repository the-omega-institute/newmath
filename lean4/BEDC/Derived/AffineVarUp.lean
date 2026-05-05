import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.AffineVarUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

def AffineFiniteFamilyZeroLocus (AffPoint : BHist -> Prop)
    (PolyEvalZero : BHist -> BHist -> Prop) (family : ProbeBundle BHist) (x : BHist) :
    Prop :=
  AffPoint x ∧ forall {p : BHist}, InBundle p family -> PolyEvalZero p x

theorem AffineFiniteFamilyZeroLocus_intersection_concat {AffPoint : BHist -> Prop}
    {PolyEvalZero : BHist -> BHist -> Prop} {F G : ProbeBundle BHist} {x : BHist} :
    AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero (bundleAppend F G) x <->
      AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero F x ∧
        AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero G x := by
  constructor
  · intro locus
    constructor
    · exact And.intro locus.left
        (by
          intro p memberF
          exact locus.right
            (Iff.mpr inBundle_bundleAppend_iff (Or.inl memberF)))
    · exact And.intro locus.left
        (by
          intro p memberG
          exact locus.right
            (Iff.mpr inBundle_bundleAppend_iff (Or.inr memberG)))
  · intro loci
    exact And.intro loci.left.left
      (by
        intro p member
        cases Iff.mp inBundle_bundleAppend_iff member with
        | inl memberF =>
            exact loci.left.right memberF
        | inr memberG =>
            exact loci.right.right memberG)

theorem AffineFiniteFamilyZeroLocus_empty_family_iff {AffPoint : BHist -> Prop}
    {PolyEvalZero : BHist -> BHist -> Prop} {x : BHist} :
    AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero ProbeBundle.Bnil x <-> AffPoint x := by
  constructor
  · intro locus
    exact locus.left
  · intro point
    exact And.intro point
      (by
        intro p member
        exact False.elim (inBundle_nil_elim member))

end BEDC.Derived.AffineVarUp
