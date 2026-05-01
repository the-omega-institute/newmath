import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def PairFrame : BHist → BHist → BHist
  | BHist.Empty, tail => BHist.e0 tail
  | BHist.e0 head, tail => BHist.e1 (BHist.e0 (PairFrame head tail))
  | BHist.e1 head, tail => BHist.e1 (BHist.e1 (PairFrame head tail))

def FramedListEndpoint : ListCarrier BHist → BHist
  | [] => BHist.e0 BHist.Empty
  | head :: tail => BHist.e1 (PairFrame head (FramedListEndpoint tail))

def FramedListSpineRep (A : BHist -> Prop) (h : BHist) (xs : ListCarrier BHist) :
    Prop :=
  (forall x : BHist, x ∈ xs -> A x) /\ hsame h (FramedListEndpoint xs)

theorem FramedListSpineRep_hsame_transport {A : BHist -> Prop} {h h' : BHist}
    {xs : ListCarrier BHist} :
    FramedListSpineRep A h xs -> hsame h h' -> FramedListSpineRep A h' xs := by
  intro rep same
  cases rep with
  | intro entries endpoint =>
      constructor
      · exact entries
      · exact hsame_trans (hsame_symm same) endpoint

theorem PairFrame_congruence {u u' t t' : BHist} :
    hsame u u' -> hsame t t' -> hsame (PairFrame u t) (PairFrame u' t') := by
  intro sameU sameT
  cases sameU
  cases sameT
  exact hsame_refl (PairFrame u t)

theorem PairFrame_hsame_injective {u u' t t' : BHist} :
    hsame (PairFrame u t) (PairFrame u' t') → hsame u u' ∧ hsame t t' := by
  intro same
  induction u generalizing u' t t' with
  | Empty =>
      cases u' with
      | Empty =>
          change hsame (BHist.e0 t) (BHist.e0 t') at same
          constructor
          · rfl
          · exact hsame_e0_iff.mp same
      | e0 u' =>
          change hsame (BHist.e0 t) (BHist.e1 (BHist.e0 (PairFrame u' t'))) at same
          exact False.elim (not_hsame_e0_e1 same)
      | e1 u' =>
          change hsame (BHist.e0 t) (BHist.e1 (BHist.e1 (PairFrame u' t'))) at same
          exact False.elim (not_hsame_e0_e1 same)
  | e0 u ih =>
      cases u' with
      | Empty =>
          change hsame (BHist.e1 (BHist.e0 (PairFrame u t))) (BHist.e0 t') at same
          exact False.elim (not_hsame_e1_e0 same)
      | e0 u' =>
          change hsame (BHist.e1 (BHist.e0 (PairFrame u t)))
            (BHist.e1 (BHist.e0 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e0 (PairFrame u t)) (BHist.e0 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          have recursive :
              hsame u u' ∧ hsame t t' :=
            ih (u' := u') (t := t) (t' := t') (hsame_e0_iff.mp inner)
          constructor
          · exact hsame_e0_congr recursive.left
          · exact recursive.right
      | e1 u' =>
          change hsame (BHist.e1 (BHist.e0 (PairFrame u t)))
            (BHist.e1 (BHist.e1 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e0 (PairFrame u t)) (BHist.e1 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          exact False.elim (not_hsame_e0_e1 inner)
  | e1 u ih =>
      cases u' with
      | Empty =>
          change hsame (BHist.e1 (BHist.e1 (PairFrame u t))) (BHist.e0 t') at same
          exact False.elim (not_hsame_e1_e0 same)
      | e0 u' =>
          change hsame (BHist.e1 (BHist.e1 (PairFrame u t)))
            (BHist.e1 (BHist.e0 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e1 (PairFrame u t)) (BHist.e0 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          exact False.elim (not_hsame_e1_e0 inner)
      | e1 u' =>
          change hsame (BHist.e1 (BHist.e1 (PairFrame u t)))
            (BHist.e1 (BHist.e1 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e1 (PairFrame u t)) (BHist.e1 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          have recursive :
              hsame u u' ∧ hsame t t' :=
            ih (u' := u') (t := t) (t' := t') (hsame_e1_iff.mp inner)
          constructor
          · exact hsame_e1_congr recursive.left
          · exact recursive.right

theorem FramedListEndpoint_no_confusion_cons_inversion {a b : BHist}
    {xs ys : ListCarrier BHist} :
    (hsame (FramedListEndpoint []) (FramedListEndpoint (a :: xs)) → False) ∧
      (hsame (FramedListEndpoint (a :: xs)) (FramedListEndpoint []) → False) ∧
        (hsame (FramedListEndpoint (a :: xs)) (FramedListEndpoint (b :: ys)) →
          hsame a b ∧ hsame (FramedListEndpoint xs) (FramedListEndpoint ys)) := by
  constructor
  · intro same
    change hsame (BHist.e0 BHist.Empty)
      (BHist.e1 (PairFrame a (FramedListEndpoint xs))) at same
    exact not_hsame_e0_e1 same
  · constructor
    · intro same
      change hsame (BHist.e1 (PairFrame a (FramedListEndpoint xs)))
        (BHist.e0 BHist.Empty) at same
      exact not_hsame_e1_e0 same
    · intro same
      change hsame (BHist.e1 (PairFrame a (FramedListEndpoint xs)))
        (BHist.e1 (PairFrame b (FramedListEndpoint ys))) at same
      exact PairFrame_hsame_injective (hsame_e1_iff.mp same)

theorem FramedListEndpoint_classifier_exactness {xs ys : ListCarrier BHist} :
    hsame (FramedListEndpoint xs) (FramedListEndpoint ys) <->
      ListClassifierSpec hsame xs ys := by
  constructor
  · intro same
    induction xs generalizing ys with
    | nil =>
        cases ys with
        | nil =>
            constructor
        | cons y ys =>
            exact False.elim
              ((FramedListEndpoint_no_confusion_cons_inversion
                (a := y) (b := y) (xs := ys) (ys := ys)).left same)
    | cons x xs ih =>
        cases ys with
        | nil =>
            exact False.elim
              ((FramedListEndpoint_no_confusion_cons_inversion
                (a := x) (b := x) (xs := xs) (ys := xs)).right.left same)
        | cons y ys =>
            have split :
                hsame x y ∧ hsame (FramedListEndpoint xs) (FramedListEndpoint ys) :=
              (FramedListEndpoint_no_confusion_cons_inversion
                (a := x) (b := y) (xs := xs) (ys := ys)).right.right same
            constructor
            · exact split.left
            · exact ih split.right
  · intro classifier
    induction xs generalizing ys with
    | nil =>
        cases ys with
        | nil =>
            exact hsame_refl (FramedListEndpoint [])
        | cons _ _ =>
            cases classifier
    | cons x xs ih =>
        cases ys with
        | nil =>
            cases classifier
        | cons y ys =>
            cases classifier with
            | intro headSame tailSame =>
                change hsame (BHist.e1 (PairFrame x (FramedListEndpoint xs)))
                  (BHist.e1 (PairFrame y (FramedListEndpoint ys)))
                exact hsame_e1_congr (PairFrame_congruence headSame (ih tailSame))

theorem FramedListEndpoint_length_preservation {xs ys : ListCarrier BHist} :
    hsame (FramedListEndpoint xs) (FramedListEndpoint ys) -> xs.length = ys.length := by
  intro same
  exact ListClassifierSpec_hsame_length_eq (FramedListEndpoint_classifier_exactness.mp same)

def ListSourceHsameCompatible (A : BHist → Prop) (Rel : BHist → BHist → Prop) :
    Prop :=
  ∀ {a b : BHist}, A a → A b → hsame a b → Rel a b

theorem FramedListSpineRep_coherence {A : BHist → Prop} {Rel : BHist → BHist → Prop}
    (compat : ListSourceHsameCompatible A Rel) :
    ∀ {h : BHist} {xs ys : ListCarrier BHist},
      FramedListSpineRep A h xs →
        FramedListSpineRep A h ys → ListClassifierSpec Rel xs ys := by
  intro h xs
  induction xs generalizing h with
  | nil =>
      intro ys repX repY
      cases repX with
      | intro _ endpointX =>
          cases repY with
          | intro _ endpointY =>
              have sameEndpoints : hsame (FramedListEndpoint []) (FramedListEndpoint ys) :=
                hsame_trans (hsame_symm endpointX) endpointY
              cases ys with
              | nil =>
                  constructor
              | cons y ys =>
                  exact False.elim
                    ((FramedListEndpoint_no_confusion_cons_inversion
                      (a := y) (b := y) (xs := ys) (ys := ys)).left sameEndpoints)
  | cons x xs ih =>
      intro ys repX repY
      cases repX with
      | intro entriesX endpointX =>
          cases repY with
          | intro entriesY endpointY =>
              have sameEndpoints :
                  hsame (FramedListEndpoint (x :: xs)) (FramedListEndpoint ys) :=
                hsame_trans (hsame_symm endpointX) endpointY
              cases ys with
              | nil =>
                  exact False.elim
                    ((FramedListEndpoint_no_confusion_cons_inversion
                      (a := x) (b := x) (xs := xs) (ys := xs)).right.left
                        sameEndpoints)
              | cons y ys =>
                  have split :
                      hsame x y ∧
                        hsame (FramedListEndpoint xs) (FramedListEndpoint ys) :=
                    (FramedListEndpoint_no_confusion_cons_inversion
                      (a := x) (b := y) (xs := xs) (ys := ys)).right.right
                        sameEndpoints
                  constructor
                  · exact compat
                      (entriesX x (List.Mem.head xs))
                      (entriesY y (List.Mem.head ys))
                      split.left
                  · have entriesXTail : ∀ z : BHist, z ∈ xs → A z := by
                      intro z memZ
                      exact entriesX z (List.Mem.tail x memZ)
                    have entriesYTail : ∀ z : BHist, z ∈ ys → A z := by
                      intro z memZ
                      exact entriesY z (List.Mem.tail y memZ)
                    exact ih
                      (h := FramedListEndpoint xs)
                      (And.intro entriesXTail (hsame_refl (FramedListEndpoint xs)))
                      (And.intro entriesYTail split.right)

theorem FramedListSpineRep_length_determinism {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (compat : ListSourceHsameCompatible A Rel)
    {h : BHist} {xs ys : ListCarrier BHist} :
    FramedListSpineRep A h xs →
      FramedListSpineRep A h ys → xs.length = ys.length := by
  intro repX repY
  have classified : ListClassifierSpec Rel xs ys :=
    FramedListSpineRep_coherence compat repX repY
  have classifier_length :
      ∀ {xs ys : ListCarrier BHist}, ListClassifierSpec Rel xs ys → xs.length = ys.length := by
    intro xs
    induction xs with
    | nil =>
        intro ys same
        cases ys with
        | nil =>
            rfl
        | cons _ _ =>
            cases same
    | cons _ xs ih =>
        intro ys same
        cases ys with
        | nil =>
            cases same
        | cons _ ys =>
            cases same with
            | intro _ tailClassified =>
                exact congrArg Nat.succ (ih tailClassified)
  exact classifier_length classified

theorem ListClassifierSpec_symm_from_nameCert {Carrier : BHist → Prop}
    {Rel : BHist → BHist → Prop} (cert : NameCert Carrier Rel) :
    ∀ {xs ys : ListCarrier BHist},
      ListClassifierSpec Rel xs ys → ListClassifierSpec Rel ys xs := by
  intro xs
  induction xs with
  | nil =>
      intro ys classified
      cases ys with
      | nil =>
          constructor
      | cons _ _ =>
          cases classified
  | cons _ xs ih =>
      intro ys classified
      cases ys with
      | nil =>
          cases classified
      | cons _ _ =>
          cases classified with
          | intro headClassified tailClassified =>
              constructor
              · exact cert.equiv_symm headClassified
              · exact ih tailClassified

def FramedListBridgeClassifier (A : BHist → Prop) (Rel : BHist → BHist → Prop)
    (h k : BHist) : Prop :=
  ∃ xs ys : ListCarrier BHist,
    FramedListSpineRep A h xs ∧
      FramedListSpineRep A k ys ∧ ListClassifierSpec Rel xs ys

theorem FramedListBridgeClassifier_displayed_spine_exactness
    {A : BHist → Prop} {Rel : BHist → BHist → Prop}
    (cert : NameCert A Rel) (compat : ListSourceHsameCompatible A Rel)
    {h k : BHist} {xs ys : ListCarrier BHist} :
    FramedListSpineRep A h xs →
      FramedListSpineRep A k ys →
        (FramedListBridgeClassifier A Rel h k ↔ ListClassifierSpec Rel xs ys) := by
  intro repH repK
  constructor
  · intro bridge
    cases bridge with
    | intro xs0 bridgeRest =>
        cases bridgeRest with
        | intro ys0 bridgeData =>
            cases bridgeData with
            | intro repH0 bridgeTail =>
                cases bridgeTail with
                | intro repK0 classifiedBridge =>
                    have classifiedLeft : ListClassifierSpec Rel xs xs0 :=
                      FramedListSpineRep_coherence compat repH repH0
                    have classifiedRightForward : ListClassifierSpec Rel ys ys0 :=
                      FramedListSpineRep_coherence compat repK repK0
                    have classifiedRight : ListClassifierSpec Rel ys0 ys :=
                      ListClassifierSpec_symm_from_nameCert cert classifiedRightForward
                    exact ListClassifierSpec_trans_from_nameCert cert
                      (ListClassifierSpec_trans_from_nameCert cert
                        classifiedLeft classifiedBridge)
                      classifiedRight
  · intro classified
    exact Exists.intro xs
      (Exists.intro ys (And.intro repH (And.intro repK classified)))

theorem FramedListBridgeClassifier_represented_length {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (compat : ListSourceHsameCompatible A Rel)
    {h k : BHist} {xs0 ys0 : ListCarrier BHist} :
    FramedListSpineRep A h xs0 →
      FramedListSpineRep A k ys0 →
        FramedListBridgeClassifier A Rel h k → xs0.length = ys0.length := by
  intro repH repK bridge
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro repHX bridgeRest =>
              cases bridgeRest with
              | intro repKY classifiedBridge =>
                  have classifiedLeft : ListClassifierSpec Rel xs0 xs :=
                    FramedListSpineRep_coherence compat repH repHX
                  have classifiedRight : ListClassifierSpec Rel ys0 ys :=
                    FramedListSpineRep_coherence compat repK repKY
                  have classifierLength :
                      ∀ {xs ys : ListCarrier BHist},
                        ListClassifierSpec Rel xs ys → xs.length = ys.length := by
                    intro xs
                    induction xs with
                    | nil =>
                        intro ys classified
                        cases ys with
                        | nil =>
                            rfl
                        | cons _ _ =>
                            cases classified
                    | cons _ xs ih =>
                        intro ys classified
                        cases ys with
                        | nil =>
                            cases classified
                        | cons _ ys =>
                            cases classified with
                            | intro _ tailClassified =>
                                exact congrArg Nat.succ (ih tailClassified)
                  exact Eq.trans (classifierLength classifiedLeft)
                    (Eq.trans (classifierLength classifiedBridge)
                      (Eq.symm (classifierLength classifiedRight)))

end BEDC.Derived.ListUp
