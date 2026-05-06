import BEDC.Derived.ListUp.PublicLength

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def FramedListPublicAppend (A : BHist -> Prop) (h k r : BHist) : Prop :=
  ∃ xs ys : ListCarrier BHist,
    FramedListSpineRep A h xs ∧ FramedListSpineRep A k ys ∧
      FramedListSpineRep A r (xs ++ ys)

theorem FramedListPublicAppend_public_length_classifier_transport {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h h' k k' r r' : BHist} :
    FramedListPublicAppend A h k r ->
      FramedListBridgeClassifier A Rel h h' ->
        FramedListBridgeClassifier A Rel k k' ->
          FramedListBridgeClassifier A Rel r r' ->
            exists u : Nat, exists v : Nat, exists w : Nat,
              FramedListPublicLength A h u ∧ FramedListPublicLength A h' u ∧
                FramedListPublicLength A k v ∧ FramedListPublicLength A k' v ∧
                  FramedListPublicLength A r w ∧ FramedListPublicLength A r' w ∧
                    w = u + v := by
  intro appendWitness bridgeH bridgeK bridgeR
  cases appendWitness with
  | intro xs rest =>
      cases rest with
      | intro ys reps =>
          cases reps with
          | intro repH reps =>
              cases reps with
              | intro repK repR =>
                  have publicH : FramedListPublicLength A h xs.length :=
                    Exists.intro xs (And.intro repH rfl)
                  have publicK : FramedListPublicLength A k ys.length :=
                    Exists.intro ys (And.intro repK rfl)
                  have publicR : FramedListPublicLength A r (xs ++ ys).length :=
                    Exists.intro (xs ++ ys) (And.intro repR rfl)
                  have transportH :=
                    (FramedListPublicLength_classifier_transport
                      (A := A) (Rel := Rel) cert compat bridgeH).left publicH
                  have transportK :=
                    (FramedListPublicLength_classifier_transport
                      (A := A) (Rel := Rel) cert compat bridgeK).left publicK
                  have transportR :=
                    (FramedListPublicLength_classifier_transport
                      (A := A) (Rel := Rel) cert compat bridgeR).left publicR
                  have appendLengthPure :
                      ∀ xs ys : ListCarrier BHist,
                        (xs ++ ys).length = xs.length + ys.length := by
                    intro left
                    induction left with
                    | nil =>
                        intro right
                        exact (Nat.zero_add right.length).symm
                    | cons _ tail ih =>
                        intro right
                        exact (congrArg Nat.succ (ih right)).trans
                          (Nat.succ_add tail.length right.length).symm
                  have appendLength : (xs ++ ys).length = xs.length + ys.length := by
                    exact appendLengthPure xs ys
                  exact ⟨xs.length, ys.length, (xs ++ ys).length, publicH, transportH,
                    publicK, transportK, publicR, transportR, appendLength⟩

end BEDC.Derived.ListUp
