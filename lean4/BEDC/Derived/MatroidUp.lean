import BEDC.Derived.FinsetUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.MatroidUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.Derived.FinsetUp

namespace Hsame

def MatroidFinSetSubset (E J I : BHist -> Prop) : Prop :=
  (exists xs : ProbeBundle BHist, FinsetEnumerationBundle E xs ∧
    forall z : BHist, J z <-> FinsetEnumerationCarrier E hsame xs z) ∧
    forall z : BHist, J z -> I z

def MatroidFinSetIntersection (E J I K : BHist -> Prop) : Prop :=
  exists xs : ProbeBundle BHist, FinsetEnumerationBundle E xs ∧
    (forall z : BHist, J z <-> FinsetEnumerationCarrier E hsame xs z) ∧
      forall z : BHist, J z <-> I z ∧ K z

theorem MatroidFinSetIntersection_left_subset {E I K J : BHist -> Prop} :
    MatroidFinSetIntersection E J I K -> MatroidFinSetSubset E J I := by
  intro intersection
  cases intersection with
  | intro xs data =>
      cases data with
      | intro spine rest =>
          cases rest with
          | intro enumerates pointwise =>
              constructor
              · exact Exists.intro xs (And.intro spine enumerates)
              · intro z memberJ
                exact (Iff.mp (pointwise z) memberJ).left

end Hsame

def MatroidFinsetEnumerates
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (bundle : ProbeBundle BHist) (J : BHist -> Prop) : Prop :=
  FinsetEnumerationBundle E bundle ∧
    forall z : BHist, J z <-> FinsetEnumerationCarrier E Rel bundle z

def MatroidFinsetSubset
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (J I : BHist -> Prop) : Prop :=
  (exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J) ∧
    forall z : BHist, J z -> I z

def MatroidFinsetIntersection
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (J I K : BHist -> Prop) : Prop :=
  exists zs : ProbeBundle BHist,
    MatroidFinsetEnumerates E Rel zs J ∧ forall z : BHist, J z <-> I z ∧ K z

theorem MatroidFinsetIntersection_left_subset
    {E : BHist -> Prop} {Rel : BHist -> BHist -> Prop} {I K J : BHist -> Prop} :
    MatroidFinsetIntersection E Rel J I K ->
      MatroidFinsetSubset E Rel J I ∧
        exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J := by
  intro intersection
  cases intersection with
  | intro zs data =>
      cases data with
      | intro enumerates pointwise =>
          have finiteSpine :
              exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J :=
            Exists.intro zs enumerates
          have subset : MatroidFinsetSubset E Rel J I := by
            constructor
            · exact finiteSpine
            · intro z memberJ
              exact (Iff.mp (pointwise z) memberJ).left
          exact And.intro subset finiteSpine

theorem MatroidIntersection_preserves_independence
    {E : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {Ind : (BHist -> Prop) -> Prop} {I K J : BHist -> Prop} :
    (forall {A B : BHist -> Prop}, Ind A -> MatroidFinsetSubset E Rel B A -> Ind B) ->
      Ind I ->
        MatroidFinsetIntersection E Rel J I K ->
          Ind J ∧ exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J := by
  intro hereditary independentI intersection
  have subsetAndWitness :=
    MatroidFinsetIntersection_left_subset (E := E) (Rel := Rel) (I := I) (K := K)
      (J := J) intersection
  constructor
  · exact hereditary independentI subsetAndWitness.left
  · exact subsetAndWitness.right

def MatroidFinSetSpineEnumerates (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (xs : ProbeBundle BHist) (S : BHist -> Prop) : Prop :=
  (forall x : BHist, InBundle x xs -> E x) ∧
    (forall z : BHist, S z <-> exists x : BHist, InBundle x xs ∧ Rel z x)

theorem MatroidFinSetSpineEnumerates_classifier_saturation {E K : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : BEDC.FKernel.NameCert.NameCert E Rel)
    {ks : ProbeBundle BHist} :
    MatroidFinSetSpineEnumerates E Rel ks K -> forall {x y : BHist}, K x -> E y ->
      Rel y x -> K y := by
  intro enumerates x y memberX _carrierY relYX
  have memberWitness : exists k : BHist, InBundle k ks ∧ Rel x k :=
    Iff.mp (enumerates.right x) memberX
  cases memberWitness with
  | intro k witness =>
      have relXK : Rel x k := witness.right
      have relYK : Rel y k :=
        BEDC.FKernel.NameCert.NameCert.equiv_trans cert relYX relXK
      exact Iff.mpr (enumerates.right y) (Exists.intro k (And.intro witness.left relYK))

def MatroidFinSetIntersection (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (J I K : BHist -> Prop) : Prop :=
  exists xs : ProbeBundle BHist,
    MatroidFinSetSpineEnumerates E Rel xs J ∧ forall z : BHist, J z <-> I z ∧ K z

theorem MatroidFinSetIntersection_left_subset {E : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {I K J : BHist -> Prop} :
    MatroidFinSetIntersection E Rel J I K ->
      exists xs : ProbeBundle BHist,
        MatroidFinSetSpineEnumerates E Rel xs J ∧ forall z : BHist, J z -> I z := by
  intro intersection
  cases intersection with
  | intro xs data =>
      exact Exists.intro xs
        (And.intro data.left
          (by
            intro z memberJ
            exact (Iff.mp (data.right z) memberJ).left))

theorem MatroidFinSetIntersection_preserves_independence {E : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {I K J : BHist -> Prop}
    {Ind : (BHist -> Prop) -> Prop}
    (hereditary : forall {U V : BHist -> Prop},
      (exists xs : ProbeBundle BHist,
        MatroidFinSetSpineEnumerates E Rel xs U ∧ forall z : BHist, U z -> V z) ->
        Ind V -> Ind U) :
    Ind I -> MatroidFinSetIntersection E Rel J I K ->
      exists xs : ProbeBundle BHist, MatroidFinSetSpineEnumerates E Rel xs J ∧ Ind J := by
  intro independentI intersection
  have leftSubset := MatroidFinSetIntersection_left_subset intersection
  cases leftSubset with
  | intro xs data =>
      have finiteSubset :
          exists xs : ProbeBundle BHist,
            MatroidFinSetSpineEnumerates E Rel xs J ∧ forall z : BHist, J z -> I z :=
        Exists.intro xs data
      exact Exists.intro xs (And.intro data.left (hereditary finiteSubset independentI))

end BEDC.Derived.MatroidUp
