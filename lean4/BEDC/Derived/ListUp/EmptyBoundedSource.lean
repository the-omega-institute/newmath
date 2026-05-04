import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

def ListHsameEmptyBoundedSource (A : BHist → Prop) : Prop :=
  ∀ {a : BHist}, A a → hsame a BHist.Empty

theorem ListHsameEmptyBoundedSource_equal_length_classifier {A : BHist → Prop}
    (bounded : ListHsameEmptyBoundedSource A) :
    ∀ {xs ys : ListCarrier BHist},
      (∀ x : BHist, x ∈ xs → A x) →
        (∀ y : BHist, y ∈ ys → A y) →
          xs.length = ys.length → ListClassifierSpec hsame xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys _entriesX entriesY sameLength
      cases ys with
      | nil =>
          constructor
      | cons y ys =>
          cases sameLength
  | cons x xs ih =>
      intro ys entriesX entriesY sameLength
      cases ys with
      | nil =>
          cases sameLength
      | cons y ys =>
          constructor
          · exact hsame_trans (bounded (entriesX x (List.Mem.head xs)))
              (hsame_symm (bounded (entriesY y (List.Mem.head ys))))
          · have tailLength : xs.length = ys.length := Nat.succ.inj sameLength
            exact ih
              (by
                intro z memZ
                exact entriesX z (List.Mem.tail x memZ))
              (by
                intro z memZ
                exact entriesY z (List.Mem.tail y memZ))
              tailLength

end BEDC.Derived.ListUp
