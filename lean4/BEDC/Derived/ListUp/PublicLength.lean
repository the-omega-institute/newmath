import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.Derived.ListUp.Length

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def FramedListPublicLength (A : BHist → Prop) (h : BHist) (n : Nat) : Prop :=
  ∃ xs : ListCarrier BHist, FramedListSpineRep A h xs ∧ xs.length = n

theorem FramedListPublicLength_constructor_endpoint_readback {A : BHist → Prop}
    {h : BHist} {n : Nat} :
    (FramedListPublicLength A h 0 ↔ hsame h (BHist.e0 BHist.Empty)) ∧
      (FramedListPublicLength A h (Nat.succ n) →
        ∃ a : BHist, ∃ xs : ListCarrier BHist,
          A a ∧ FramedListSpineRep A h (a :: xs) ∧
            FramedListPublicLength A (FramedListEndpoint xs) n) := by
  constructor
  · constructor
    · intro publicLength
      cases publicLength with
      | intro xs data =>
          cases data with
          | intro rep lengthEq =>
              cases xs with
              | nil =>
                  exact rep.right
              | cons _ _ =>
                  cases lengthEq
    · intro sameEndpoint
      exact Exists.intro []
        (And.intro
          (And.intro
            (fun x mem => by
              cases mem)
            sameEndpoint)
          rfl)
  · intro publicLength
    cases publicLength with
    | intro xs data =>
        cases data with
        | intro rep lengthEq =>
            cases xs with
            | nil =>
                cases lengthEq
            | cons a tail =>
                have tailLength : tail.length = n :=
                  Nat.succ.inj lengthEq
                have tailEntries : ∀ x : BHist, x ∈ tail → A x := by
                  intro x mem
                  exact rep.left x (List.Mem.tail a mem)
                have tailPublic : FramedListPublicLength A (FramedListEndpoint tail) n :=
                  Exists.intro tail
                    (And.intro
                      (And.intro tailEntries (hsame_refl (FramedListEndpoint tail)))
                      tailLength)
                exact Exists.intro a
                  (Exists.intro tail
                    (And.intro
                      (rep.left a (List.Mem.head tail))
                      (And.intro rep tailPublic)))

theorem FramedListPublicLength_well_defined {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (compat : ListSourceHsameCompatible A Rel) :
    (∀ {h : BHist} {n m : Nat},
      FramedListPublicLength A h n → FramedListPublicLength A h m → n = m) ∧
      (∀ {h k : BHist} {n : Nat},
        FramedListBridgeClassifier A Rel h k →
          FramedListPublicLength A h n → FramedListPublicLength A k n) := by
  constructor
  · intro h n m publicN publicM
    cases publicN with
    | intro xs dataN =>
        cases dataN with
        | intro repX lengthX =>
            cases publicM with
            | intro ys dataM =>
                cases dataM with
                | intro repY lengthY =>
                    have sameLength : xs.length = ys.length :=
                      FramedListSpineRep_length_determinism compat repX repY
                    exact Eq.trans (Eq.symm lengthX) (Eq.trans sameLength lengthY)
  · intro h k n bridge publicN
    cases publicN with
    | intro xs0 dataN =>
        cases dataN with
        | intro repH0 lengthX0 =>
            cases bridge with
            | intro xs bridgeTail =>
                cases bridgeTail with
                | intro ys bridgeData =>
                    cases bridgeData with
                    | intro _repH bridgeRest =>
                        cases bridgeRest with
                        | intro repK _classified =>
                            have sameLength : xs0.length = ys.length :=
                              FramedListBridgeClassifier_represented_length compat repH0
                                repK
                                (Exists.intro xs
                                  (Exists.intro ys
                                    (And.intro _repH (And.intro repK _classified))))
                            exact Exists.intro ys
                              (And.intro repK (Eq.trans (Eq.symm sameLength) lengthX0))

theorem FramedListBridgeClassifier_public_length_total {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} :
    FramedListBridgeClassifier A Rel h k →
      (FramedListHistoryCarrier A h ∧ FramedListHistoryCarrier A k) ∧
        ∃ n : Nat, FramedListPublicLength A h n ∧ FramedListPublicLength A k n := by
  intro bridge
  have carriers :
      FramedListHistoryCarrier A h ∧ FramedListHistoryCarrier A k :=
    (FramedListBridgeClassifier_equivalence_fields cert compat).right.left bridge
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro repH bridgeRest =>
              cases bridgeRest with
              | intro repK classified =>
                  have sameLength : xs.length = ys.length :=
                    ListClassifierSpec_length_eq classified
                  exact And.intro carriers
                    (Exists.intro xs.length
                      (And.intro
                        (Exists.intro xs (And.intro repH rfl))
                        (Exists.intro ys (And.intro repK sameLength.symm))))

end BEDC.Derived.ListUp
