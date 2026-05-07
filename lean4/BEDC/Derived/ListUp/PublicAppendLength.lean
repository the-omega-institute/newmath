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

theorem FramedListPublicAppend_total_and_classifier_congruent {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) :
    (forall {h k : BHist}, FramedListHistoryCarrier A h -> FramedListHistoryCarrier A k ->
      exists r : BHist, FramedListPublicAppend A h k r ∧ FramedListHistoryCarrier A r) ∧
      (forall {h h' k k' r r' : BHist}, FramedListBridgeClassifier A Rel h h' ->
        FramedListBridgeClassifier A Rel k k' -> FramedListPublicAppend A h k r ->
          FramedListPublicAppend A h' k' r' -> FramedListBridgeClassifier A Rel r r') ∧
        (forall {h k r r' : BHist}, FramedListPublicAppend A h k r ->
          FramedListPublicAppend A h k r' -> FramedListBridgeClassifier A Rel r r') := by
  have appendClass :
      forall {xs ys zs ws : ListCarrier BHist},
        ListClassifierSpec Rel xs ys -> ListClassifierSpec Rel zs ws ->
          ListClassifierSpec Rel (xs ++ zs) (ys ++ ws) := by
    intro xs
    induction xs with
    | nil =>
        intro ys zs ws sameXY sameZW
        cases ys with
        | nil =>
            exact sameZW
        | cons _ _ =>
            cases sameXY
    | cons _ xs ih =>
        intro ys zs ws sameXY sameZW
        cases ys with
        | nil =>
            cases sameXY
        | cons _ ys =>
            cases sameXY with
            | intro sameHead sameTail =>
                constructor
                · exact sameHead
                · exact ih sameTail sameZW
  constructor
  · intro h k carrierH carrierK
    cases carrierH with
    | intro xs repH =>
        cases carrierK with
        | intro ys repK =>
            let r := FramedListEndpoint (xs ++ ys)
            have repR : FramedListSpineRep A r (xs ++ ys) := by
              constructor
              · intro z memZ
                have split := List.mem_append.mp memZ
                cases split with
                | inl memX =>
                    exact repH.left z memX
                | inr memY =>
                    exact repK.left z memY
              · exact hsame_refl r
            exact Exists.intro r
              (And.intro
                (Exists.intro xs
                  (Exists.intro ys
                    (And.intro repH (And.intro repK repR))))
                (Exists.intro (xs ++ ys) repR))
  · constructor
    · intro h h' k k' r r' bridgeH bridgeK appendR appendR'
      cases appendR with
      | intro xs appendTail =>
          cases appendTail with
          | intro ys appendData =>
              cases appendData with
              | intro repH appendRest =>
                  cases appendRest with
                  | intro repK repR =>
                      cases appendR' with
                      | intro xs' appendTail' =>
                          cases appendTail' with
                          | intro ys' appendData' =>
                              cases appendData' with
                              | intro repH' appendRest' =>
                                  cases appendRest' with
                                  | intro repK' repR' =>
                                      have sameHeads : ListClassifierSpec Rel xs xs' :=
                                        (FramedListBridgeClassifier_displayed_spine_exactness
                                          cert compat repH repH').mp bridgeH
                                      have sameTails : ListClassifierSpec Rel ys ys' :=
                                        (FramedListBridgeClassifier_displayed_spine_exactness
                                          cert compat repK repK').mp bridgeK
                                      have sameAppended :
                                          ListClassifierSpec Rel (xs ++ ys) (xs' ++ ys') :=
                                        appendClass sameHeads sameTails
                                      exact
                                        (FramedListBridgeClassifier_displayed_spine_exactness
                                          cert compat repR repR').mpr sameAppended
    · intro h k r r' appendR appendR'
      cases appendR with
      | intro xs appendTail =>
          cases appendTail with
          | intro ys appendData =>
              cases appendData with
              | intro repH appendRest =>
                  cases appendRest with
                  | intro repK repR =>
                      cases appendR' with
                      | intro xs' appendTail' =>
                          cases appendTail' with
                          | intro ys' appendData' =>
                              cases appendData' with
                              | intro repH' appendRest' =>
                                  cases appendRest' with
                                  | intro repK' repR' =>
                                      have sameHeads : ListClassifierSpec Rel xs xs' :=
                                        FramedListSpineRep_coherence compat repH repH'
                                      have sameTails : ListClassifierSpec Rel ys ys' :=
                                        FramedListSpineRep_coherence compat repK repK'
                                      have sameAppended :
                                          ListClassifierSpec Rel (xs ++ ys) (xs' ++ ys') :=
                                        appendClass sameHeads sameTails
                                      exact
                                        (FramedListBridgeClassifier_displayed_spine_exactness
                                          cert compat repR repR').mpr sameAppended

end BEDC.Derived.ListUp
