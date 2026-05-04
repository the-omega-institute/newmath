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

theorem FramedListBridgeClassifier_successor_component_exactness_iff
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    (FramedListBridgeClassifier A Rel h k ∧ FramedListPublicLength A h (Nat.succ n) ∧
      FramedListPublicLength A k (Nat.succ n)) ↔
      ∃ a b : BHist, ∃ xs ys : ListCarrier BHist,
        A a ∧ A b ∧ FramedListSpineRep A h (a :: xs) ∧
          FramedListSpineRep A k (b :: ys) ∧
            FramedListPublicLength A (FramedListEndpoint xs) n ∧
              FramedListPublicLength A (FramedListEndpoint ys) n ∧ Rel a b ∧
                FramedListBridgeClassifier A Rel (FramedListEndpoint xs)
                  (FramedListEndpoint ys) := by
  constructor
  · intro data
    have readH := FramedListPublicLength_constructor_endpoint_readback.right data.right.left
    have readK := FramedListPublicLength_constructor_endpoint_readback.right data.right.right
    cases readH with
    | intro a tailH =>
        cases tailH with
        | intro xs packH =>
            cases readK with
            | intro b tailK =>
                cases tailK with
                | intro ys packK =>
                    have split :=
                      ((FramedListBridgeClassifier_constructor_exactness cert compat).right.right.right
                        packH.right.left packK.right.left).mp data.left
                    have tailRepH : FramedListSpineRep A (FramedListEndpoint xs) xs := by
                      constructor
                      · intro z memZ
                        exact packH.right.left.left z (List.Mem.tail a memZ)
                      · exact hsame_refl (FramedListEndpoint xs)
                    have tailRepK : FramedListSpineRep A (FramedListEndpoint ys) ys := by
                      constructor
                      · intro z memZ
                        exact packK.right.left.left z (List.Mem.tail b memZ)
                      · exact hsame_refl (FramedListEndpoint ys)
                    have tailBridge :
                        FramedListBridgeClassifier A Rel (FramedListEndpoint xs)
                          (FramedListEndpoint ys) :=
                      (FramedListBridgeClassifier_displayed_spine_exactness cert compat
                        tailRepH tailRepK).mpr split.right
                    exact ⟨a, b, xs, ys, packH.left, packK.left, packH.right.left,
                      packK.right.left, packH.right.right, packK.right.right,
                        split.left, tailBridge⟩
  · intro data
    cases data with
    | intro a rest =>
        cases rest with
        | intro b rest =>
            cases rest with
            | intro xs rest =>
                cases rest with
                | intro ys pack =>
                    have tailRepH : FramedListSpineRep A (FramedListEndpoint xs) xs := by
                      constructor
                      · intro z memZ
                        exact pack.right.right.left.left z (List.Mem.tail a memZ)
                      · exact hsame_refl (FramedListEndpoint xs)
                    have tailRepK : FramedListSpineRep A (FramedListEndpoint ys) ys := by
                      constructor
                      · intro z memZ
                        exact pack.right.right.right.left.left z (List.Mem.tail b memZ)
                      · exact hsame_refl (FramedListEndpoint ys)
                    have tailClassified : ListClassifierSpec Rel xs ys :=
                      (FramedListBridgeClassifier_displayed_spine_exactness cert compat
                        tailRepH tailRepK).mp pack.right.right.right.right.right.right.right
                    have bridge : FramedListBridgeClassifier A Rel h k :=
                      ((FramedListBridgeClassifier_constructor_exactness cert compat).right.right.right
                        pack.right.right.left pack.right.right.right.left).mpr
                        ⟨pack.right.right.right.right.right.right.left, tailClassified⟩
                    have publicH : FramedListPublicLength A h (Nat.succ n) := by
                      cases pack.right.right.right.right.left with
                      | intro xs0 tailPublic =>
                          have sameLength := FramedListSpineRep_length_determinism compat
                            tailRepH tailPublic.left
                          exact ⟨a :: xs,
                            pack.right.right.left,
                              congrArg Nat.succ (Eq.trans sameLength tailPublic.right)⟩
                    have publicK : FramedListPublicLength A k (Nat.succ n) := by
                      cases pack.right.right.right.right.right.left with
                      | intro ys0 tailPublic =>
                          have sameLength := FramedListSpineRep_length_determinism compat
                            tailRepK tailPublic.left
                          exact ⟨b :: ys,
                            pack.right.right.right.left,
                              congrArg Nat.succ (Eq.trans sameLength tailPublic.right)⟩
                    exact ⟨bridge, publicH, publicK⟩

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

theorem FramedListPublicLength_classifier_transport {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    FramedListBridgeClassifier A Rel h k ->
      (FramedListPublicLength A h n -> FramedListPublicLength A k n) ∧
        (FramedListPublicLength A k n -> FramedListPublicLength A h n) := by
  intro bridge
  have forward :
      FramedListPublicLength A h n -> FramedListPublicLength A k n :=
    (FramedListPublicLength_well_defined compat).right bridge
  have bridgeSymm : FramedListBridgeClassifier A Rel k h :=
    (FramedListBridgeClassifier_equivalence_fields cert compat).right.right.left bridge
  have backward :
      FramedListPublicLength A k n -> FramedListPublicLength A h n :=
    (FramedListPublicLength_well_defined compat).right bridgeSymm
  exact And.intro forward backward

end BEDC.Derived.ListUp
