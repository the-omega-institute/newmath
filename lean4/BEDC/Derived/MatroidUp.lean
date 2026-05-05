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

def MatroidFinSetInsert
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (x : BHist) (I J : BHist -> Prop) : Prop :=
  exists xs : ProbeBundle BHist,
    MatroidFinsetEnumerates E Rel xs I ∧
      forall z : BHist, J z <-> I z ∨ Rel z x

def MatroidExchangeRow
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (FinSetCardLt : (BHist -> Prop) -> (BHist -> Prop) -> Prop)
    (Ind : (BHist -> Prop) -> Prop) : Prop :=
  forall {I J : BHist -> Prop},
    Ind I -> Ind J -> FinSetCardLt I J ->
      exists x : BHist, J x ∧
        exists Insert : BHist -> Prop, MatroidFinSetInsert E Rel x I Insert ∧ Ind Insert

structure MatroidRestrictionRows
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop) (K : BHist -> Prop)
    (FinSetCardLt : (BHist -> Prop) -> (BHist -> Prop) -> Prop)
    (Ind IndRestr : (BHist -> Prop) -> Prop) : Prop where
  finite : forall {I : BHist -> Prop}, IndRestr I ->
    exists xs : ProbeBundle BHist, MatroidFinSetSpineEnumerates E Rel xs I
  ground : forall {I : BHist -> Prop}, IndRestr I -> forall z : BHist, I z -> K z
  empty : IndRestr (fun _z : BHist => False)
  hereditary : forall {I J : BHist -> Prop},
    IndRestr I -> MatroidFinsetSubset E Rel J I -> IndRestr J
  exchange : MatroidExchangeRow E Rel FinSetCardLt IndRestr

theorem MatroidFinSetInsert_subset_of_restricted_member
    {E : BHist -> Prop} {Rel : BHist -> BHist -> Prop} {K I Insert : BHist -> Prop}
    {x : BHist} (cert : NameCert E Rel)
    (subsetK : MatroidFinsetSubset E Rel K E)
    (subsetI : MatroidFinsetSubset E Rel I K)
    (memberK : K x)
    (insertRow : MatroidFinSetInsert E Rel x I Insert) :
    MatroidFinsetSubset E Rel Insert K := by
  cases insertRow with
  | intro xs insertFields =>
      cases insertFields with
      | intro enumI pointwise =>
          have sourceX : E x := subsetK.right x memberK
          constructor
          · exact Exists.intro (ProbeBundle.Bcons x xs)
              (And.intro
                (And.intro sourceX enumI.left)
                (by
                  intro z
                  constructor
                  · intro memberInsert
                    cases Iff.mp (pointwise z) memberInsert with
                    | inl memberI =>
                        have carriedI : FinsetEnumerationCarrier E Rel xs z :=
                          Iff.mp (enumI.right z) memberI
                        cases carriedI with
                        | intro sourceZ witness =>
                            exact And.intro sourceZ
                              (by
                                cases witness with
                                | intro w memberAndRel =>
                                    exact Exists.intro w
                                      (And.intro (Or.inr memberAndRel.left)
                                        memberAndRel.right))
                    | inr relZX =>
                        exact And.intro
                          (NameCert.carrier_respects_equiv cert
                            (NameCert.equiv_symm cert relZX) sourceX)
                          (Exists.intro x (And.intro (Or.inl rfl) relZX))
                  · intro carried
                    cases carried with
                    | intro sourceZ witness =>
                        cases witness with
                        | intro w memberAndRel =>
                            cases memberAndRel with
                            | intro memberCons relZW =>
                                cases memberCons with
                                | inl sameWX =>
                                    cases sameWX
                                    exact Iff.mpr (pointwise z) (Or.inr relZW)
                                | inr memberXs =>
                                    have carriedI : FinsetEnumerationCarrier E Rel xs z :=
                                      And.intro sourceZ
                                        (Exists.intro w (And.intro memberXs relZW))
                                    exact Iff.mpr (pointwise z)
                                      (Or.inl (Iff.mpr (enumI.right z) carriedI))))
          · intro z memberInsert
            cases Iff.mp (pointwise z) memberInsert with
            | inl memberI =>
                exact subsetI.right z memberI
            | inr relZX =>
                cases subsetK.left with
                | intro ks enumK =>
                    have carriedKX : FinsetEnumerationCarrier E Rel ks x :=
                      Iff.mp (enumK.right x) memberK
                    cases carriedKX with
                    | intro _sourceX witness =>
                        cases witness with
                        | intro w memberAndRel =>
                            exact Iff.mpr (enumK.right z)
                              (And.intro
                                (NameCert.carrier_respects_equiv cert
                                  (NameCert.equiv_symm cert relZX) sourceX)
                                (Exists.intro w
                                  (And.intro memberAndRel.left
                                    (NameCert.equiv_trans cert relZX memberAndRel.right))))

theorem MatroidRestrictionRows_certificate
    {E : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {Ind IndRestr : (BHist -> Prop) -> Prop} {K : BHist -> Prop}
    {FinSetCardLt : (BHist -> Prop) -> (BHist -> Prop) -> Prop}
    (cert : NameCert E Rel)
    (subsetK : MatroidFinsetSubset E Rel K E)
    (finiteM : forall {I : BHist -> Prop}, Ind I ->
      exists xs : ProbeBundle BHist, MatroidFinSetSpineEnumerates E Rel xs I)
    (emptyM : Ind (fun _z : BHist => False))
    (hereditaryM : forall {I J : BHist -> Prop},
      Ind I -> MatroidFinsetSubset E Rel J I -> Ind J)
    (exchangeM : MatroidExchangeRow E Rel FinSetCardLt Ind)
    (restrictEq : forall I : BHist -> Prop,
      IndRestr I <-> Ind I ∧ MatroidFinsetSubset E Rel I K) :
    MatroidRestrictionRows E Rel K FinSetCardLt Ind IndRestr := by
  have subsetKWitness : exists xs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel xs K :=
    subsetK.left
  exact {
    finite := by
      intro I independentRestr
      exact finiteM (Iff.mp (restrictEq I) independentRestr).left
    ground := by
      intro I independentRestr z memberI
      exact (Iff.mp (restrictEq I) independentRestr).right.right z memberI
    empty := by
      apply Iff.mpr (restrictEq (fun _z : BHist => False))
      constructor
      · exact emptyM
      · constructor
        · exact Exists.intro ProbeBundle.Bnil
            (And.intro
              (hsame_refl BHist.Empty)
              (by
                intro z
                constructor
                · intro emptyMember
                  exact False.elim emptyMember
                · intro carried
                  cases carried.right with
                  | intro x memberAndRel =>
                      exact False.elim memberAndRel.left))
        · intro z emptyMember
          exact False.elim emptyMember
    hereditary := by
      intro I J independentRestr subsetJI
      have independentI : Ind I := (Iff.mp (restrictEq I) independentRestr).left
      have subsetIK : MatroidFinsetSubset E Rel I K :=
        (Iff.mp (restrictEq I) independentRestr).right
      apply Iff.mpr (restrictEq J)
      constructor
      · exact hereditaryM independentI subsetJI
      · constructor
        · exact subsetJI.left
        · intro z memberJ
          exact subsetIK.right z (subsetJI.right z memberJ)
    exchange := by
      intro I J independentIRestr independentJRestr cardLt
      have independentI : Ind I := (Iff.mp (restrictEq I) independentIRestr).left
      have independentJ : Ind J := (Iff.mp (restrictEq J) independentJRestr).left
      have subsetIK : MatroidFinsetSubset E Rel I K :=
        (Iff.mp (restrictEq I) independentIRestr).right
      have subsetJK : MatroidFinsetSubset E Rel J K :=
        (Iff.mp (restrictEq J) independentJRestr).right
      cases exchangeM independentI independentJ cardLt with
      | intro x exchangeData =>
          cases exchangeData with
          | intro memberJ insertData =>
              cases insertData with
              | intro Insert insertAndIndependent =>
                  cases insertAndIndependent with
                  | intro insertRow independentInsert =>
                      have memberK : K x := subsetJK.right x memberJ
                      have insertK : MatroidFinsetSubset E Rel Insert K :=
                        MatroidFinSetInsert_subset_of_restricted_member cert subsetK subsetIK memberK
                          insertRow
                      exact Exists.intro x
                        (And.intro memberJ
                          (Exists.intro Insert
                            (And.intro insertRow
                              (Iff.mpr (restrictEq Insert)
                        (And.intro independentInsert insertK)))))
  }

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
