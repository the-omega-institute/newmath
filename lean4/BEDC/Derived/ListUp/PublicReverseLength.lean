import BEDC.Derived.ListUp.PublicLength
import BEDC.Derived.ListUp.PublicReverse

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem FramedListPublicReverse_public_length_transport {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} :
    (∃ xs : ListCarrier BHist, FramedListSpineRep A h xs ∧
      FramedListSpineRep A k xs.reverse) →
      (∀ {n : Nat}, FramedListPublicLength A h n → FramedListPublicLength A k n) ∧
        (∀ {n : Nat}, FramedListPublicLength A k n → FramedListPublicLength A h n) := by
  intro reverseData
  have appendAssocPure :
      ∀ xs ys zs : ListCarrier BHist, (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
    intro xs
    induction xs with
    | nil =>
        intro ys zs
        rfl
    | cons x xs ih =>
        intro ys zs
        exact congrArg (List.cons x) (ih ys zs)
  have appendNilPure : ∀ xs : ListCarrier BHist, xs ++ [] = xs := by
    intro xs
    induction xs with
    | nil =>
        rfl
    | cons x xs ih =>
        exact congrArg (List.cons x) ih
  have reverseAuxPure :
      ∀ xs ys : ListCarrier BHist, List.reverseAux xs ys = List.reverseAux xs [] ++ ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys
        rfl
    | cons x xs ih =>
        intro ys
        exact (ih (x :: ys)).trans
          ((appendAssocPure (List.reverseAux xs []) [x] ys).symm.trans
            (congrArg (fun tail => tail ++ ys) (ih [x]).symm))
  have reverseConsPure :
      ∀ x : BHist, ∀ xs : ListCarrier BHist, List.reverse (x :: xs) = xs.reverse ++ [x] := by
    intro x xs
    change List.reverseAux xs [x] = List.reverseAux xs [] ++ [x]
    exact reverseAuxPure xs [x]
  have appendSingletonLength :
      ∀ xs : ListCarrier BHist, ∀ x : BHist, (xs ++ [x]).length = Nat.succ xs.length := by
    intro xs
    induction xs with
    | nil =>
        intro x
        rfl
    | cons head tail ih =>
        intro x
        exact congrArg Nat.succ (ih x)
  have reverseLengthPure :
      ∀ xs : ListCarrier BHist, xs.reverse.length = xs.length := by
    intro xs
    induction xs with
    | nil =>
        rfl
    | cons x xs ih =>
        exact (congrArg List.length (reverseConsPure x xs)).trans
          ((appendSingletonLength xs.reverse x).trans (congrArg Nat.succ ih))
  have reverseFacts :=
    FramedListPublicReverse_functional_involutive (A := A) (Rel := Rel) cert compat
  constructor
  · intro n publicH
    cases reverseData with
    | intro xs reverseReps =>
        cases publicH with
        | intro ys publicData =>
            cases publicData with
            | intro repY lengthY =>
                have sameLengthYX : ys.length = xs.length :=
                  FramedListSpineRep_length_determinism compat repY reverseReps.left
                have reverseLengthX : xs.reverse.length = xs.length :=
                  reverseLengthPure xs
                exact Exists.intro xs.reverse
                  (And.intro reverseReps.right
                    (Eq.trans reverseLengthX (Eq.trans (Eq.symm sameLengthYX) lengthY)))
  · intro n publicK
    have reverseBack :
        ∃ xs : ListCarrier BHist,
          FramedListSpineRep A k xs ∧ FramedListSpineRep A h xs.reverse :=
      reverseFacts.right.left reverseData
    cases reverseBack with
    | intro xs reverseReps =>
        cases publicK with
        | intro ys publicData =>
            cases publicData with
            | intro repY lengthY =>
                have sameLengthYX : ys.length = xs.length :=
                  FramedListSpineRep_length_determinism compat repY reverseReps.left
                have reverseLengthX : xs.reverse.length = xs.length :=
                  reverseLengthPure xs
                exact Exists.intro xs.reverse
                  (And.intro reverseReps.right
                    (Eq.trans reverseLengthX (Eq.trans (Eq.symm sameLengthYX) lengthY)))

end BEDC.Derived.ListUp
