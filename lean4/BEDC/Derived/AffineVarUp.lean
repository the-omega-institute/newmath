import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.AffineVarUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

def AffineFiniteFamilyZeroLocus (AffPoint : BHist -> Prop)
    (PolyEvalZero : BHist -> BHist -> Prop) (family : ProbeBundle BHist) (x : BHist) :
    Prop :=
  AffPoint x ∧ forall {p : BHist}, InBundle p family -> PolyEvalZero p x

def AffineFiniteFamilyEquationInclusion (F G : ProbeBundle BHist) : Prop :=
  forall {p : BHist}, InBundle p F -> InBundle p G

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

theorem AffineFiniteFamilyEquationRows_restrict {PolyEvalZero : BHist -> BHist -> Prop}
    {F G : ProbeBundle BHist} {x : BHist} :
    AffineFiniteFamilyEquationInclusion F G ->
      (forall {p : BHist}, InBundle p G -> PolyEvalZero p x) ->
        forall {p : BHist}, InBundle p F -> PolyEvalZero p x := by
  intro incl rows p memberF
  exact rows (incl memberF)

theorem AffineFiniteFamilyZeroLocus_inclusion_contravariant {AffPoint : BHist -> Prop}
    {PolyEvalZero : BHist -> BHist -> Prop} {F G : ProbeBundle BHist} {x : BHist} :
    AffineFiniteFamilyEquationInclusion F G ->
      AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero G x ->
        AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero F x := by
  intro incl locusG
  exact And.intro locusG.left (AffineFiniteFamilyEquationRows_restrict incl locusG.right)

theorem AffineFiniteFamilyZeroLocus_inclusion_reverse {AffPoint : BHist -> Prop}
    {PolyEvalZero : BHist -> BHist -> Prop} {F G : ProbeBundle BHist} {x : BHist} :
    (forall {p : BHist}, InBundle p F -> InBundle p G) ->
      AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero G x ->
        AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero F x := by
  intro inclusion locusG
  exact And.intro locusG.left
    (by
      intro p memberF
      exact locusG.right (inclusion memberF))

theorem AffineFiniteFamilyZeroLocus_occurred_equation_row {AffPoint : BHist -> Prop}
    {PolyEvalZero : BHist -> BHist -> Prop} {F : ProbeBundle BHist} {p x : BHist} :
    InBundle p F -> AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero F x ->
      PolyEvalZero p x := by
  intro member locus
  exact locus.right member

theorem AffineFiniteFamilyZeroLocus_duplicate_head_insert {AffPoint : BHist -> Prop}
    {PolyEvalZero : BHist -> BHist -> Prop} {F : ProbeBundle BHist} {p x : BHist} :
    InBundle p F ->
      (AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero (ProbeBundle.Bcons p F) x <->
        AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero F x) := by
  intro memberP
  constructor
  · intro locus
    exact And.intro locus.left
      (by
        intro q memberQ
        exact locus.right (Or.inr memberQ))
  · intro locus
    exact And.intro locus.left
      (by
        intro q member
        cases member with
        | inl sameHead =>
            cases sameHead
            exact locus.right memberP
        | inr memberTail =>
            exact locus.right memberTail)

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

theorem AffineFiniteFamilyZeroLocus_mutual_inclusion_iff {AffPoint : BHist -> Prop}
    {PolyEvalZero : BHist -> BHist -> Prop} {F G : ProbeBundle BHist} {x : BHist} :
    AffineFiniteFamilyEquationInclusion F G ->
      AffineFiniteFamilyEquationInclusion G F ->
        (AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero F x <->
          AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero G x) := by
  intro inclFG inclGF
  constructor
  · intro locusF
    exact AffineFiniteFamilyZeroLocus_inclusion_contravariant inclGF locusF
  · intro locusG
    exact AffineFiniteFamilyZeroLocus_inclusion_contravariant inclFG locusG

end BEDC.Derived.AffineVarUp
