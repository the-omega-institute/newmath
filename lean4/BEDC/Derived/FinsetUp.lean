import BEDC.FKernel.Hist
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FinsetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert

def FinsetEnumerationBundle (A : BHist -> Prop) : ProbeBundle BHist -> Prop
  | ProbeBundle.Bnil => hsame BHist.Empty BHist.Empty
  | ProbeBundle.Bcons x xs => A x ∧ FinsetEnumerationBundle A xs

theorem FinsetEnumerationBundle_member_source_carried {A : BHist -> Prop} {x : BHist}
    {xs : ProbeBundle BHist} :
    FinsetEnumerationBundle A xs -> InBundle x xs -> A x := by
  intro spine member
  induction xs with
  | Bnil =>
      cases member
  | Bcons y ys ih =>
      cases spine with
      | intro sourceY spineYS =>
          cases member with
          | inl same =>
              cases same
              exact sourceY
          | inr tailMember =>
              exact ih spineYS tailMember

def FinsetEnumerationCarrier
    (A : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (bundle : ProbeBundle BHist) (a : BHist) : Prop :=
  A a ∧ exists x : BHist, InBundle x bundle ∧ Rel a x

def FinsetEnumerationClassifier
    (A : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (left right : ProbeBundle BHist) : Prop :=
  forall z : BHist,
    FinsetEnumerationCarrier A Rel left z <-> FinsetEnumerationCarrier A Rel right z

theorem FinsetEnumerationCarrier_membership_exactness
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (cert : NameCert A Rel) {bundle : ProbeBundle BHist}
    (bundleCarrier : FinsetEnumerationBundle A bundle) {a : BHist} :
    FinsetEnumerationCarrier A Rel bundle a <->
      exists x : BHist, InBundle x bundle /\ Rel a x := by
  constructor
  · intro carried
    exact carried.right
  · intro witness
    cases witness with
    | intro x memberAndSame =>
        have sourceX : A x :=
          FinsetEnumerationBundle_member_source_carried bundleCarrier memberAndSame.left
        have sourceA : A a :=
          NameCert.carrier_respects_equiv cert
            (NameCert.equiv_symm cert memberAndSame.right) sourceX
        exact And.intro sourceA (Exists.intro x memberAndSame)

theorem FinsetEnumerationClassifier_duplicate_insert
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    {bundle : ProbeBundle BHist} {x y : BHist}
    (bundleCarrier : FinsetEnumerationBundle A bundle) (sourceX : A x)
    (memberY : InBundle y bundle) (sameXY : Rel x y) :
    FinsetEnumerationClassifier A Rel (ProbeBundle.Bcons x bundle) bundle := by
  intro z
  constructor
  · intro carried
    exact Iff.mpr
      (FinsetEnumerationCarrier_membership_exactness cert bundleCarrier)
      (by
        cases carried.right with
        | intro w memberAndSame =>
            cases memberAndSame.left with
            | inl sameWX =>
                cases sameWX
                have sameZY : Rel z y :=
                  NameCert.equiv_trans cert memberAndSame.right sameXY
                exact Exists.intro y (And.intro memberY sameZY)
            | inr memberTail =>
                exact Exists.intro w (And.intro memberTail memberAndSame.right))
  · intro carried
    have consCarrier :
        FinsetEnumerationBundle A (ProbeBundle.Bcons x bundle) :=
      And.intro sourceX bundleCarrier
    cases carried.right with
    | intro w memberAndSame =>
        exact Iff.mpr
          (FinsetEnumerationCarrier_membership_exactness cert consCarrier)
          (Exists.intro w (And.intro (Or.inr memberAndSame.left) memberAndSame.right))

theorem FinsetEnumerationClassifier_trans
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {xs ys zs : ProbeBundle BHist} :
    FinsetEnumerationClassifier A Rel xs ys ->
      FinsetEnumerationClassifier A Rel ys zs ->
        FinsetEnumerationClassifier A Rel xs zs := by
  intro xy yz z
  change FinsetEnumerationCarrier A Rel xs z <-> FinsetEnumerationCarrier A Rel zs z
  constructor
  · intro carried
    exact Iff.mp (yz z) (Iff.mp (xy z) carried)
  · intro carried
    exact Iff.mpr (xy z) (Iff.mpr (yz z) carried)

theorem FinsetEnumerationClassifier_symm
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {left right : ProbeBundle BHist} :
    FinsetEnumerationClassifier A Rel left right ->
      FinsetEnumerationClassifier A Rel right left := by
  intro classified z
  constructor
  · intro carriedRight
    exact Iff.mpr (classified z) carriedRight
  · intro carriedLeft
    exact Iff.mp (classified z) carriedLeft

theorem FinsetEnumerationCarrier_bundleAppend_split
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {left right : ProbeBundle BHist} {a : BHist} :
    FinsetEnumerationCarrier A Rel (bundleAppend left right) a ↔
      A a ∧
        ((exists x : BHist, InBundle x left ∧ Rel a x) ∨
          (exists x : BHist, InBundle x right ∧ Rel a x)) := by
  constructor
  · intro carried
    cases carried with
    | intro source witness =>
        constructor
        · exact source
        · cases witness with
          | intro x memberAndRel =>
              cases memberAndRel with
              | intro member rel =>
                  have split :
                      InBundle x left ∨ InBundle x right :=
                    (inBundle_bundleAppend_iff (p := x) (left := left) (right := right)).mp
                      member
                  cases split with
                  | inl memberLeft =>
                      exact Or.inl (Exists.intro x (And.intro memberLeft rel))
                  | inr memberRight =>
                      exact Or.inr (Exists.intro x (And.intro memberRight rel))
  · intro carried
    cases carried with
    | intro source split =>
        constructor
        · exact source
        · cases split with
          | inl leftWitness =>
              cases leftWitness with
              | intro x memberAndRel =>
                  cases memberAndRel with
                  | intro member rel =>
                      have memberApp :
                          InBundle x (bundleAppend left right) :=
                        (inBundle_bundleAppend_iff (p := x) (left := left) (right := right)).mpr
                          (Or.inl member)
                      exact Exists.intro x (And.intro memberApp rel)
          | inr rightWitness =>
              cases rightWitness with
              | intro x memberAndRel =>
                  cases memberAndRel with
                  | intro member rel =>
                      have memberApp :
                          InBundle x (bundleAppend left right) :=
                        (inBundle_bundleAppend_iff (p := x) (left := left) (right := right)).mpr
                          (Or.inr member)
                      exact Exists.intro x (And.intro memberApp rel)

theorem FinsetEnumerationCarrier_append_split
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {left right : ProbeBundle BHist} {z : BHist} :
    FinsetEnumerationCarrier A Rel (bundleAppend left right) z <->
      FinsetEnumerationCarrier A Rel left z ∨ FinsetEnumerationCarrier A Rel right z := by
  constructor
  · intro carried
    cases carried with
    | intro sourceZ witness =>
        cases witness with
        | intro x memberAndSame =>
            have splitMember : InBundle x left ∨ InBundle x right :=
              Iff.mp inBundle_bundleAppend_iff memberAndSame.left
            cases splitMember with
            | inl leftMember =>
                exact Or.inl
                  (And.intro sourceZ (Exists.intro x (And.intro leftMember memberAndSame.right)))
            | inr rightMember =>
                exact Or.inr
                  (And.intro sourceZ (Exists.intro x (And.intro rightMember memberAndSame.right)))
  · intro carried
    cases carried with
    | inl leftCarried =>
        cases leftCarried with
        | intro sourceZ witness =>
            cases witness with
            | intro x memberAndSame =>
                have appendMember : InBundle x (bundleAppend left right) :=
                  Iff.mpr inBundle_bundleAppend_iff (Or.inl memberAndSame.left)
                exact And.intro sourceZ
                  (Exists.intro x (And.intro appendMember memberAndSame.right))
    | inr rightCarried =>
        cases rightCarried with
        | intro sourceZ witness =>
            cases witness with
            | intro x memberAndSame =>
                have appendMember : InBundle x (bundleAppend left right) :=
                  Iff.mpr inBundle_bundleAppend_iff (Or.inr memberAndSame.left)
                exact And.intro sourceZ
                  (Exists.intro x (And.intro appendMember memberAndSame.right))

theorem FinsetEnumerationCarrier_bundleAppend_union
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    {left right : ProbeBundle BHist} {U V : BHist -> Prop} :
    (forall z : BHist, FinsetEnumerationCarrier A Rel left z <-> U z) ->
      (forall z : BHist, FinsetEnumerationCarrier A Rel right z <-> V z) ->
        forall z : BHist,
          FinsetEnumerationCarrier A Rel (bundleAppend left right) z <-> U z \/ V z := by
  intro leftEnumerates rightEnumerates z
  constructor
  · intro carried
    have split :
        FinsetEnumerationCarrier A Rel left z ∨ FinsetEnumerationCarrier A Rel right z :=
      Iff.mp FinsetEnumerationCarrier_append_split carried
    cases split with
    | inl leftCarried =>
        exact Or.inl (Iff.mp (leftEnumerates z) leftCarried)
    | inr rightCarried =>
        exact Or.inr (Iff.mp (rightEnumerates z) rightCarried)
  · intro unionCarried
    have split :
        FinsetEnumerationCarrier A Rel left z ∨ FinsetEnumerationCarrier A Rel right z := by
      cases unionCarried with
      | inl carriedU =>
          exact Or.inl (Iff.mpr (leftEnumerates z) carriedU)
      | inr carriedV =>
          exact Or.inr (Iff.mpr (rightEnumerates z) carriedV)
    exact Iff.mpr FinsetEnumerationCarrier_append_split split

def FinsetEnumerationPermutation
    (_A : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (left right : ProbeBundle BHist) : Prop :=
  (forall {p : BHist}, InBundle p left -> exists q : BHist, InBundle q right ∧ Rel p q) ∧
    (forall {q : BHist}, InBundle q right -> exists p : BHist, InBundle p left ∧ Rel q p)

theorem FinsetEnumerationPermutation_refl
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    {xs : ProbeBundle BHist} (bundleCarrier : FinsetEnumerationBundle A xs) :
    FinsetEnumerationPermutation A Rel xs xs := by
  constructor
  · intro p member
    have sourceP : A p :=
      FinsetEnumerationBundle_member_source_carried bundleCarrier member
    exact Exists.intro p (And.intro member (NameCert.equiv_refl cert sourceP))
  · intro p member
    have sourceP : A p :=
      FinsetEnumerationBundle_member_source_carried bundleCarrier member
    exact Exists.intro p (And.intro member (NameCert.equiv_refl cert sourceP))

theorem FinsetEnumerationPermutation_trans
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (cert : NameCert A Rel) {xs ys zs : ProbeBundle BHist} :
    FinsetEnumerationPermutation A Rel xs ys ->
      FinsetEnumerationPermutation A Rel ys zs ->
        FinsetEnumerationPermutation A Rel xs zs := by
  intro xy yz
  constructor
  · intro p memberXs
    cases xy.left memberXs with
    | intro q qData =>
        cases yz.left qData.left with
        | intro r rData =>
            exact Exists.intro r
              (And.intro rData.left
                (NameCert.equiv_trans cert qData.right rData.right))
  · intro r memberZs
    cases yz.right memberZs with
    | intro q qData =>
        cases xy.right qData.left with
        | intro p pData =>
            exact Exists.intro p
              (And.intro pData.left
                (NameCert.equiv_trans cert qData.right pData.right))

theorem FinsetEnumerationPermutation_symm
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (cert : NameCert A Rel) {xs ys : ProbeBundle BHist} :
    FinsetEnumerationPermutation A Rel xs ys ->
      FinsetEnumerationPermutation A Rel ys xs := by
  intro permutation
  constructor
  · intro q memberYs
    cases permutation.right memberYs with
    | intro p pData =>
        have relPQ : Rel p q := NameCert.equiv_symm cert pData.right
        exact Exists.intro p
          (And.intro pData.left (NameCert.equiv_symm cert relPQ))
  · intro p memberXs
    cases permutation.left memberXs with
    | intro q qData =>
        have relQP : Rel q p := NameCert.equiv_symm cert qData.right
        exact Exists.intro q
          (And.intro qData.left (NameCert.equiv_symm cert relQP))

theorem FinsetEnumerationClassifier_permutation_invariant
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    {left right : ProbeBundle BHist}
    (leftBundle : FinsetEnumerationBundle A left)
    (rightBundle : FinsetEnumerationBundle A right)
    (forward : forall {p : BHist}, InBundle p left ->
      exists q : BHist, InBundle q right ∧ Rel p q)
    (backward : forall {q : BHist}, InBundle q right ->
      exists p : BHist, InBundle p left ∧ Rel q p) :
    FinsetEnumerationClassifier A Rel left right := by
  intro z
  constructor
  · intro carriedLeft
    cases carriedLeft with
    | intro _sourceZ witness =>
        cases witness with
        | intro p memberAndRel =>
            cases memberAndRel with
            | intro memberLeft relZP =>
                cases forward memberLeft with
                | intro q rightData =>
                    have relZQ : Rel z q :=
                      NameCert.equiv_trans cert relZP rightData.right
                    have sourceQ : A q :=
                      FinsetEnumerationBundle_member_source_carried rightBundle rightData.left
                    have sourceRightZ : A z :=
                      NameCert.carrier_respects_equiv cert
                        (NameCert.equiv_symm cert relZQ) sourceQ
                    exact And.intro sourceRightZ
                      (Exists.intro q
                        (And.intro rightData.left relZQ))
  · intro carriedRight
    cases carriedRight with
    | intro _sourceZ witness =>
        cases witness with
        | intro q memberAndRel =>
            cases memberAndRel with
            | intro memberRight relZQ =>
                cases backward memberRight with
                | intro p leftData =>
                    have relZP : Rel z p :=
                      NameCert.equiv_trans cert relZQ leftData.right
                    have sourceP : A p :=
                      FinsetEnumerationBundle_member_source_carried leftBundle leftData.left
                    have sourceLeftZ : A z :=
                      NameCert.carrier_respects_equiv cert
                        (NameCert.equiv_symm cert relZP) sourceP
                    exact And.intro sourceLeftZ
                      (Exists.intro p
                        (And.intro leftData.left relZP))

end BEDC.Derived.FinsetUp
