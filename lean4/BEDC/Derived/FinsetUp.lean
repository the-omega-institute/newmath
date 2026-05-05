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

end BEDC.Derived.FinsetUp
