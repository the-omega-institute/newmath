import BEDC.Derived.ListUp.FramedEndpoint

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

theorem FramedListBridgeClassifier_public_successor_component_exactness
    {A : BHist → Prop} {Rel : BHist → BHist → Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    (FramedListBridgeClassifier A Rel h k ∧
      FramedListPublicLength A h (Nat.succ n) ∧
      FramedListPublicLength A k (Nat.succ n)) ↔
      ∃ a b : BHist, ∃ xs ys : ListCarrier BHist,
        A a ∧ A b ∧ FramedListSpineRep A h (a :: xs) ∧
        FramedListSpineRep A k (b :: ys) ∧
        FramedListPublicLength A (FramedListEndpoint xs) n ∧
        FramedListPublicLength A (FramedListEndpoint ys) n ∧
        Rel a b ∧ ListClassifierSpec Rel xs ys := by
  constructor
  · intro publicBridge
    have readH :=
      (FramedListPublicLength_constructor_endpoint_readback
        (A := A) (h := h) (n := n)).right publicBridge.right.left
    have readK :=
      (FramedListPublicLength_constructor_endpoint_readback
        (A := A) (h := k) (n := n)).right publicBridge.right.right
    cases readH with
    | intro a readHTail =>
        cases readHTail with
        | intro xs readHData =>
            cases readHData with
            | intro sourceA readHRest =>
                cases readHRest with
                | intro repH tailPublicH =>
                    cases readK with
                    | intro b readKTail =>
                        cases readKTail with
                        | intro ys readKData =>
                            cases readKData with
                            | intro sourceB readKRest =>
                                cases readKRest with
                                | intro repK tailPublicK =>
                                    have componentClassified :
                                        Rel a b ∧ ListClassifierSpec Rel xs ys :=
                                      (FramedListBridgeClassifier_constructor_exactness
                                        cert compat).right.right.right repH repK |>.mp
                                        publicBridge.left
                                    exact Exists.intro a
                                      (Exists.intro b
                                        (Exists.intro xs
                                          (Exists.intro ys
                                            (And.intro sourceA
                                              (And.intro sourceB
                                                (And.intro repH
                                                  (And.intro repK
                                                    (And.intro tailPublicH
                                                      (And.intro tailPublicK
                                                        componentClassified)))))))))
  · intro componentData
    cases componentData with
    | intro a restA =>
        cases restA with
        | intro b restB =>
            cases restB with
            | intro xs restXS =>
                cases restXS with
                | intro ys data =>
                    cases data with
                    | intro sourceA data =>
                        cases data with
                        | intro sourceB data =>
                            cases data with
                            | intro repH data =>
                                cases data with
                                | intro repK data =>
                                    cases data with
                                    | intro tailPublicH data =>
                                        cases data with
                                        | intro tailPublicK componentClassified =>
                                            have bridge : FramedListBridgeClassifier A Rel h k :=
                                              (FramedListBridgeClassifier_constructor_exactness
                                                cert compat).right.right.right repH repK |>.mpr
                                                componentClassified
                                            have tailEntriesH :
                                                ∀ z : BHist, z ∈ xs → A z := by
                                              intro z mem
                                              exact repH.left z (List.Mem.tail a mem)
                                            have canonicalTailPublicH :
                                                FramedListPublicLength A
                                                  (FramedListEndpoint xs) xs.length :=
                                              Exists.intro xs
                                                (And.intro
                                                  (And.intro tailEntriesH
                                                    (hsame_refl (FramedListEndpoint xs)))
                                                  rfl)
                                            have tailLengthH : xs.length = n :=
                                              (FramedListPublicLength_well_defined
                                                (A := A) (Rel := Rel) compat).left
                                                canonicalTailPublicH tailPublicH
                                            have publicH :
                                                FramedListPublicLength A h (Nat.succ n) :=
                                              Exists.intro (a :: xs)
                                                (And.intro repH (congrArg Nat.succ tailLengthH))
                                            have tailEntriesK :
                                                ∀ z : BHist, z ∈ ys → A z := by
                                              intro z mem
                                              exact repK.left z (List.Mem.tail b mem)
                                            have canonicalTailPublicK :
                                                FramedListPublicLength A
                                                  (FramedListEndpoint ys) ys.length :=
                                              Exists.intro ys
                                                (And.intro
                                                  (And.intro tailEntriesK
                                                    (hsame_refl (FramedListEndpoint ys)))
                                                  rfl)
                                            have tailLengthK : ys.length = n :=
                                              (FramedListPublicLength_well_defined
                                                (A := A) (Rel := Rel) compat).left
                                                canonicalTailPublicK tailPublicK
                                            have publicK :
                                                FramedListPublicLength A k (Nat.succ n) :=
                                              Exists.intro (b :: ys)
                                                (And.intro repK (congrArg Nat.succ tailLengthK))
                                            exact And.intro bridge (And.intro publicH publicK)

end BEDC.Derived.ListUp
