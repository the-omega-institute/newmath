import BEDC.Derived.FinsetUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MatroidUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem MatroidFinsetIntersection_independence_preserved
    {E : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {I K J : BHist -> Prop} {Ind : (BHist -> Prop) -> Prop}
    {xs ys : ProbeBundle BHist}
    (finiteI : MatroidFinsetEnumerates E Rel xs I)
    (finiteK : MatroidFinsetEnumerates E Rel ys K)
    (hereditary :
      forall {A B : BHist -> Prop},
        Ind A -> MatroidFinsetSubset E Rel B A -> Ind B) :
    Ind I -> MatroidFinsetIntersection E Rel J I K ->
      (exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J) ∧ Ind J := by
  intro independent intersection
  have finiteInputs :
      FinsetEnumerationBundle E xs ∧ FinsetEnumerationBundle E ys :=
    And.intro finiteI.left finiteK.left
  cases finiteInputs with
  | intro _finiteXs _finiteYs =>
      have leftRows := MatroidFinsetIntersection_left_subset intersection
      constructor
      · exact leftRows.right
      · exact hereditary independent leftRows.left

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

theorem MatroidRestrictionRows_exchange_support_boundary {E K I J : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {Ind : (BHist -> Prop) -> Prop}
    {CardLt : (BHist -> Prop) -> (BHist -> Prop) -> Prop} :
    NameCert E Rel -> (exists ks : ProbeBundle BHist, MatroidFinSetSpineEnumerates E Rel ks K) ->
      (forall {A B : BHist -> Prop}, Ind A -> Ind B -> CardLt A B -> exists x : BHist,
        exists Aplus : BHist -> Prop, B x ∧ (A x -> False) ∧
          (exists xs : ProbeBundle BHist,
            MatroidFinSetSpineEnumerates E Rel xs Aplus ∧
              forall z : BHist, Aplus z <-> A z ∨ (E z ∧ Rel z x)) ∧
            Ind Aplus) ->
        Ind I ∧ MatroidFinsetSubset E Rel I K -> Ind J ∧ MatroidFinsetSubset E Rel J K ->
          CardLt I J -> exists x : BHist, exists Iplus : BHist -> Prop,
            J x ∧ (I x -> False) ∧ K x ∧
              (exists xs : ProbeBundle BHist,
                MatroidFinSetSpineEnumerates E Rel xs Iplus ∧
                  forall z : BHist, Iplus z -> K z) ∧ Ind Iplus := by
  intro cert finiteK exchange rowsI rowsJ smaller
  cases finiteK with
  | intro ks kSpine =>
      have exchangeRows := exchange rowsI.left rowsJ.left smaller
      cases exchangeRows with
      | intro x exchangeTail =>
          cases exchangeTail with
          | intro Iplus xRows =>
              cases xRows.right.right.left with
              | intro xs insertRows =>
              have xInK : K x := rowsJ.right.right x xRows.left
              have supportInsideK : forall z : BHist, Iplus z -> K z := by
                intro z memberPlus
                have plusSplit : I z ∨ (E z ∧ Rel z x) :=
                  Iff.mp (insertRows.right z) memberPlus
                cases plusSplit with
                | inl memberI =>
                    exact rowsI.right.right z memberI
                | inr relZX =>
                    have xWitness : exists y : BHist, InBundle y ks ∧ Rel x y :=
                      Iff.mp (kSpine.right x) xInK
                    cases xWitness with
                    | intro y yRows =>
                        have relZY : Rel z y :=
                          NameCert.equiv_trans cert relZX.right yRows.right
                        exact Iff.mpr (kSpine.right z)
                          (Exists.intro y (And.intro yRows.left relZY))
              exact Exists.intro x
                (Exists.intro Iplus
                  (And.intro xRows.left
                    (And.intro xRows.right.left
                      (And.intro xInK
                        (And.intro
                          (Exists.intro xs (And.intro insertRows.left supportInsideK))
                          xRows.right.right.right)))))

end BEDC.Derived.MatroidUp
