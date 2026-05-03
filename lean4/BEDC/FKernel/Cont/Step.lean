import BEDC.FKernel.Cont
import BEDC.FKernel.Ext

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem cont_determinacy_up_to_hsame_spine {h k r r' : BHist} :
    Cont h k r -> Cont h k r' -> hsame r r' := by
  intro left right
  exact cont_deterministic left right

theorem cont_result_tag_separation {h k r0 r1 : BHist} :
    Cont h k (BHist.e0 r0) → Cont h k (BHist.e1 r1) → False := by
  intro zeroResult oneResult
  have resultSame : hsame (BHist.e0 r0) (BHist.e1 r1) :=
    cont_determinacy_up_to_hsame_spine zeroResult oneResult
  exact not_hsame_e0_e1 resultSame

theorem cont_result_hsame_tag_separation {h k r0 r1 z o : BHist} :
    Cont h k r0 -> Cont h k r1 -> hsame r0 (BHist.e0 z) ->
      hsame r1 (BHist.e1 o) -> False := by
  intro left right zeroTag oneTag
  have sameResult : hsame r0 r1 := cont_deterministic left right
  have mixed : hsame (BHist.e0 z) (BHist.e1 o) :=
    zeroTag.symm.trans (sameResult.trans oneTag)
  exact not_hsame_e0_e1 mixed

theorem cont_e0_result_witness {h k r : BHist} :
    Cont h (BHist.e0 k) r -> exists r0 : BHist, r = BHist.e0 r0 /\ Cont h k r0 := by
  intro hcont
  exact cont_step_result_inversions.left hcont

theorem cont_e1_result_witness {h k r : BHist} :
    Cont h (BHist.e1 k) r -> exists r0 : BHist, r = BHist.e1 r0 /\ Cont h k r0 := by
  intro hcont
  exact cont_step_result_inversions.right hcont

theorem cont_step_zero_iff {h k r : BHist} :
    Cont h (BHist.e0 k) (BHist.e0 r) ↔ Cont h k r := by
  constructor
  · intro hcont
    exact cont_step_rules_inversion_pair.left hcont
  · intro hcont
    exact cont_step_zero hcont

theorem cont_step_one_iff {h k r : BHist} :
    Cont h (BHist.e1 k) (BHist.e1 r) ↔ Cont h k r := by
  constructor
  · intro hcont
    exact cont_step_rules_inversion_pair.right hcont
  · intro hcont
    exact cont_step_one hcont

theorem cont_result_e0_cases_iff {h k r : BHist} :
    Cont h k (BHist.e0 r) ↔
      (k = BHist.Empty ∧ hsame h (BHist.e0 r)) ∨
        (exists k0 : BHist, k = BHist.e0 k0 ∧ Cont h k0 r) := by
  constructor
  · intro hcont
    cases k with
    | Empty =>
        exact Or.inl (And.intro rfl hcont.symm)
    | e0 k0 =>
        exact Or.inr
          (Exists.intro k0 (And.intro rfl (cont_step_zero_iff.mp hcont)))
    | e1 k0 =>
        cases hcont
  · intro data
    cases data with
    | inl emptyData =>
        cases emptyData.left
        exact emptyData.right.symm
    | inr witness =>
        cases witness with
        | intro k0 stepData =>
            cases stepData with
            | intro sameK tail =>
                cases sameK
                exact cont_step_zero tail

theorem cont_result_e1_cases_iff {h k r : BHist} :
    Cont h k (BHist.e1 r) ↔
      (k = BHist.Empty ∧ hsame h (BHist.e1 r)) ∨
        (exists k0 : BHist, k = BHist.e1 k0 ∧ Cont h k0 r) := by
  constructor
  · intro hcont
    cases k with
    | Empty =>
        exact Or.inl (And.intro rfl hcont.symm)
    | e0 k0 =>
        cases hcont
    | e1 k0 =>
        exact Or.inr
          (Exists.intro k0 (And.intro rfl (cont_step_one_iff.mp hcont)))
  · intro data
    cases data with
    | inl emptyData =>
        cases emptyData.left
        exact emptyData.right.symm
    | inr witness =>
        cases witness with
        | intro k0 stepData =>
            cases stepData with
            | intro sameK tail =>
                cases sameK
                exact cont_step_one tail

theorem cont_step_rules_iff_pair :
    (∀ {h k r : BHist}, Cont h (BHist.e0 k) (BHist.e0 r) ↔ Cont h k r) ∧
      (∀ {h k r : BHist}, Cont h (BHist.e1 k) (BHist.e1 r) ↔ Cont h k r) := by
  constructor
  · exact cont_step_zero_iff
  · exact cont_step_one_iff

theorem cont_ext_right_step {h k k' r r' : BHist} {m : BMark} :
    Cont h k r → BEDC.FKernel.Ext.Ext k m k' → BEDC.FKernel.Ext.Ext r m r' →
      Cont h k' r' := by
  intro hcont left right
  cases left
  · cases right
    exact cont_step_zero hcont
  · cases right
    exact cont_step_one hcont

theorem extension_as_singleton_continuation {h r : BHist} :
    (BEDC.FKernel.Ext.Ext h BMark.b0 r ↔ Cont h (BHist.e0 BHist.Empty) r) ∧
      (BEDC.FKernel.Ext.Ext h BMark.b1 r ↔ Cont h (BHist.e1 BHist.Empty) r) := by
  constructor
  · constructor
    · intro ext
      cases ext
      exact cont_step_zero (cont_right_unit h)
    · intro hcont
      cases cont_e0_result_witness hcont with
      | intro r0 witness =>
          cases witness with
          | intro result tail =>
              cases result
              have same : hsame r0 h := Iff.mp cont_right_unit_iff tail
              cases same
              exact BEDC.FKernel.Ext.Ext.e0 h
  · constructor
    · intro ext
      cases ext
      exact cont_step_one (cont_right_unit h)
    · intro hcont
      cases cont_e1_result_witness hcont with
      | intro r0 witness =>
          cases witness with
          | intro result tail =>
              cases result
              have same : hsame r0 h := Iff.mp cont_right_unit_iff tail
              cases same
              exact BEDC.FKernel.Ext.Ext.e1 h

theorem ext_singleton_continuation_iff_pair {h r : BHist} :
    (BEDC.FKernel.Ext.Ext h BMark.b0 r ↔ Cont h (BHist.e0 BHist.Empty) r) ∧
      (BEDC.FKernel.Ext.Ext h BMark.b1 r ↔ Cont h (BHist.e1 BHist.Empty) r) := by
  exact extension_as_singleton_continuation

theorem continuation_step_rules_iff_pair :
    (forall {h k r : BHist}, Cont h (BHist.e0 k) (BHist.e0 r) <-> Cont h k r) /\
      (forall {h k r : BHist}, Cont h (BHist.e1 k) (BHist.e1 r) <-> Cont h k r) := by
  exact cont_step_rules_iff_pair

theorem continuation_step_result_witness_iff_pair :
    (∀ {h k r : BHist},
        Cont h (BHist.e0 k) r ↔ ∃ r0 : BHist, r = BHist.e0 r0 ∧ Cont h k r0) ∧
      (∀ {h k r : BHist},
        Cont h (BHist.e1 k) r ↔ ∃ r0 : BHist, r = BHist.e1 r0 ∧ Cont h k r0) := by
  constructor
  · intro h k r
    constructor
    · intro hcont
      exact cont_step_result_inversions.left hcont
    · intro witness
      cases witness with
      | intro r0 packed =>
          cases packed with
          | intro result hcont =>
              cases result
              exact cont_step_zero hcont
  · intro h k r
    constructor
    · intro hcont
      exact cont_step_result_inversions.right hcont
    · intro witness
      cases witness with
      | intro r0 packed =>
          cases packed with
          | intro result hcont =>
              cases result
              exact cont_step_one hcont

theorem cont_step_result_witnesses_by_constructor :
    (∀ {h k r : BHist},
      Cont h (BHist.e0 k) r → ∃ r0 : BHist, r = BHist.e0 r0 ∧ Cont h k r0) ∧
      (∀ {h k r : BHist},
        Cont h (BHist.e1 k) r → ∃ r0 : BHist, r = BHist.e1 r0 ∧ Cont h k r0) := by
  constructor
  · intro h k r hcont
    exact cont_step_result_inversions.left hcont
  · intro h k r hcont
    exact cont_step_result_inversions.right hcont

theorem continuation_step_result_witnesses_pair {h k rz ro : BHist} :
    Cont h (BHist.e0 k) rz → Cont h (BHist.e1 k) ro →
      ∃ a : BHist, ∃ b : BHist,
        rz = BHist.e0 a ∧ Cont h k a ∧ ro = BHist.e1 b ∧ Cont h k b := by
  intro zeroStep oneStep
  cases cont_e0_result_witness zeroStep with
  | intro a zeroWitness =>
      cases zeroWitness with
      | intro zeroResult zeroCont =>
          cases cont_e1_result_witness oneStep with
          | intro b oneWitness =>
              cases oneWitness with
              | intro oneResult oneCont =>
                  exact Exists.intro a
                    (Exists.intro b
                      (And.intro zeroResult
                        (And.intro zeroCont (And.intro oneResult oneCont))))

theorem cont_step_result_no_confusion_pair :
    (forall {h k0 k1 r : BHist},
      Cont h (BHist.e0 k0) r -> Cont h (BHist.e1 k1) r -> False) /\
      (forall {h k0 k1 r : BHist},
        Cont h (BHist.e1 k0) r -> Cont h (BHist.e0 k1) r -> False) := by
  constructor
  · intro h k0 k1 r zeroStep oneStep
    cases cont_e0_result_witness zeroStep with
    | intro rz zeroWitness =>
        cases zeroWitness with
        | intro zeroResult _ =>
            cases zeroResult
            cases cont_e1_result_witness oneStep with
            | intro ro oneWitness =>
                cases oneWitness with
                | intro oneResult _ =>
                    cases oneResult
  · intro h k0 k1 r oneStep zeroStep
    cases cont_e1_result_witness oneStep with
    | intro ro oneWitness =>
        cases oneWitness with
        | intro oneResult _ =>
            cases oneResult
            cases cont_e0_result_witness zeroStep with
            | intro rz zeroWitness =>
                cases zeroWitness with
                | intro zeroResult _ =>
                    cases zeroResult

theorem cont_step_result_hsame_no_confusion_pair :
    (forall {h k0 k1 r0 r1 : BHist},
      Cont h (BHist.e0 k0) r0 -> Cont h (BHist.e1 k1) r1 -> hsame r0 r1 -> False) /\
      (forall {h k0 k1 r0 r1 : BHist},
        Cont h (BHist.e1 k0) r0 -> Cont h (BHist.e0 k1) r1 -> hsame r0 r1 -> False) := by
  constructor
  · intro h k0 k1 r0 r1 zeroStep oneStep same
    cases cont_e0_result_witness zeroStep with
    | intro rz zeroWitness =>
        cases zeroWitness with
        | intro zeroResult _ =>
            cases zeroResult
            cases cont_e1_result_witness oneStep with
            | intro ro oneWitness =>
                cases oneWitness with
                | intro oneResult _ =>
                    cases oneResult
                    exact not_hsame_e0_e1 same
  · intro h k0 k1 r0 r1 oneStep zeroStep same
    cases cont_e1_result_witness oneStep with
    | intro ro oneWitness =>
        cases oneWitness with
        | intro oneResult _ =>
            cases oneResult
            cases cont_e0_result_witness zeroStep with
            | intro rz zeroWitness =>
                cases zeroWitness with
                | intro zeroResult _ =>
                    cases zeroResult
                    exact not_hsame_e1_e0 same

theorem cont_step_result_not_empty_pair {h k : BHist} :
    (Cont h (BHist.e0 k) BHist.Empty → False) ∧
      (Cont h (BHist.e1 k) BHist.Empty → False) := by
  constructor
  · intro hcont
    cases hcont
  · intro hcont
    cases hcont

theorem cont_left_e0_result_iff {h k r : BHist} :
    Cont (BHist.e0 h) k (BHist.e0 r) ↔
      (k = BHist.Empty ∧ hsame h r) ∨
        (∃ k0 : BHist, k = BHist.e0 k0 ∧ Cont (BHist.e0 h) k0 r) := by
  constructor
  · intro hcont
    cases k with
    | Empty =>
        left
        constructor
        · rfl
        · exact (BHist.e0.inj hcont).symm
    | e0 k0 =>
        right
        exact Exists.intro k0 (And.intro rfl (BHist.e0.inj hcont))
    | e1 _ =>
        cases hcont
  · intro split
    cases split with
    | inl emptyCase =>
        cases emptyCase with
        | intro kEmpty same =>
            cases kEmpty
            cases same
            exact cont_right_unit (BHist.e0 h)
    | inr stepCase =>
        cases stepCase with
        | intro k0 packed =>
            cases packed with
            | intro kStep tail =>
                cases kStep
                exact cont_step_zero tail

theorem cont_left_e0_result_nonempty_tail_cases {h k r : BHist} :
    Cont (BHist.e0 h) k (BHist.e0 r) -> (hsame k BHist.Empty -> False) ->
      ∃ k0 : BHist, k = BHist.e0 k0 ∧ Cont (BHist.e0 h) k0 r := by
  intro hcont nonempty
  have splitCases := (cont_left_e0_result_iff (h := h) (k := k) (r := r)).mp hcont
  cases splitCases with
  | inl emptyCase =>
      exact False.elim (nonempty (by cases emptyCase.left; exact hsame_refl BHist.Empty))
  | inr visibleCase =>
      exact visibleCase

theorem cont_left_e1_result_cases {h k r : BHist} :
    Cont (BHist.e1 h) k (BHist.e1 r) ->
      (k = BHist.Empty ∧ hsame h r) ∨
        (∃ k0 : BHist, k = BHist.e1 k0 ∧ Cont (BHist.e1 h) k0 r) := by
  intro hcont
  cases k with
  | Empty =>
      left
      constructor
      · rfl
      · exact (BHist.e1.inj hcont).symm
  | e0 k0 =>
      cases hcont
  | e1 k0 =>
      right
      exact Exists.intro k0 (And.intro rfl (BHist.e1.inj hcont))

theorem cont_left_e1_result_iff {h k r : BHist} :
    Cont (BHist.e1 h) k (BHist.e1 r) ↔
      (k = BHist.Empty ∧ hsame h r) ∨
        (∃ k0 : BHist, k = BHist.e1 k0 ∧ Cont (BHist.e1 h) k0 r) := by
  constructor
  · intro hcont
    exact cont_left_e1_result_cases hcont
  · intro split
    cases split with
    | inl emptyCase =>
        cases emptyCase with
        | intro kEmpty same =>
            cases kEmpty
            cases same
            exact cont_right_unit (BHist.e1 h)
    | inr stepCase =>
        cases stepCase with
        | intro k0 packed =>
            cases packed with
            | intro kStep tail =>
                cases kStep
                exact cont_step_one tail

theorem cont_left_e1_result_nonempty_tail_cases {h k r : BHist} :
    Cont (BHist.e1 h) k (BHist.e1 r) -> (hsame k BHist.Empty -> False) ->
      ∃ k0 : BHist, k = BHist.e1 k0 ∧ Cont (BHist.e1 h) k0 r := by
  intro hcont nonempty
  have splitCases := cont_left_e1_result_cases hcont
  cases splitCases with
  | inl emptyCase =>
      exact False.elim (nonempty (by cases emptyCase.left; exact hsame_refl BHist.Empty))
  | inr visibleCase =>
      exact visibleCase

theorem cont_left_tag_cross_result_cases :
    (forall {h k r : BHist},
      Cont (BHist.e0 h) k (BHist.e1 r) ->
        ∃ k0 : BHist, k = BHist.e1 k0 ∧ Cont (BHist.e0 h) k0 r) ∧
      (forall {h k r : BHist},
        Cont (BHist.e1 h) k (BHist.e0 r) ->
          ∃ k0 : BHist, k = BHist.e0 k0 ∧ Cont (BHist.e1 h) k0 r) := by
  constructor
  · intro h k r hcont
    cases k with
    | Empty =>
        cases hcont
    | e0 k0 =>
        cases hcont
    | e1 k0 =>
        exact Exists.intro k0 (And.intro rfl (BHist.e1.inj hcont))
  · intro h k r hcont
    cases k with
    | Empty =>
        cases hcont
    | e0 k0 =>
        exact Exists.intro k0 (And.intro rfl (BHist.e0.inj hcont))
    | e1 k0 =>
        cases hcont

theorem cont_left_tag_cross_result_iff_pair :
    (∀ {h k r : BHist},
        Cont (BHist.e0 h) k (BHist.e1 r) ↔
          ∃ k0 : BHist, k = BHist.e1 k0 ∧ Cont (BHist.e0 h) k0 r) ∧
      (∀ {h k r : BHist},
        Cont (BHist.e1 h) k (BHist.e0 r) ↔
          ∃ k0 : BHist, k = BHist.e0 k0 ∧ Cont (BHist.e1 h) k0 r) := by
  constructor
  · intro h k r
    constructor
    · intro hcont
      exact cont_left_tag_cross_result_cases.left hcont
    · intro witness
      cases witness with
      | intro k0 packed =>
          cases packed with
          | intro kEq tail =>
              cases kEq
              exact cont_step_one tail
  · intro h k r
    constructor
    · intro hcont
      exact cont_left_tag_cross_result_cases.right hcont
    · intro witness
      cases witness with
      | intro k0 packed =>
          cases packed with
          | intro kEq tail =>
              cases kEq
              exact cont_step_zero tail

theorem cont_left_same_tag_tail_alignment :
    (forall {h k l r : BHist},
      Cont (BHist.e0 h) k (BHist.e0 r) -> Cont (BHist.e0 h) l (BHist.e0 r) ->
        (k = BHist.Empty ∧ l = BHist.Empty) ∨
          (∃ k0 l0 : BHist, k = BHist.e0 k0 ∧ l = BHist.e0 l0 ∧ hsame k0 l0)) ∧
      (forall {h k l r : BHist},
        Cont (BHist.e1 h) k (BHist.e1 r) -> Cont (BHist.e1 h) l (BHist.e1 r) ->
          (k = BHist.Empty ∧ l = BHist.Empty) ∨
            (∃ k0 l0 : BHist, k = BHist.e1 k0 ∧ l = BHist.e1 l0 ∧ hsame k0 l0)) := by
  constructor
  · intro h k l r left right
    have sameTail : hsame k l := cont_left_cancel left right
    have splitLeft := (cont_left_e0_result_iff (h := h) (k := k) (r := r)).mp left
    cases splitLeft with
    | inl emptyCase =>
        cases emptyCase with
        | intro kEmpty _sameResult =>
            cases kEmpty
            cases sameTail
            exact Or.inl (And.intro rfl rfl)
    | inr visibleCase =>
        cases visibleCase with
        | intro k0 data =>
            cases data with
            | intro kEq _tail =>
                cases kEq
                cases l with
                | Empty =>
                    cases sameTail
                | e0 l0 =>
                    exact Or.inr
                      (Exists.intro k0
                        (Exists.intro l0
                          (And.intro rfl (And.intro rfl (BHist.e0.inj sameTail)))))
                | e1 l0 =>
                    cases sameTail
  · intro h k l r left right
    have sameTail : hsame k l := cont_left_cancel left right
    have splitLeft := cont_left_e1_result_cases left
    cases splitLeft with
    | inl emptyCase =>
        cases emptyCase with
        | intro kEmpty _sameResult =>
            cases kEmpty
            cases sameTail
            exact Or.inl (And.intro rfl rfl)
    | inr visibleCase =>
        cases visibleCase with
        | intro k0 data =>
            cases data with
            | intro kEq _tail =>
                cases kEq
                cases l with
                | Empty =>
                    cases sameTail
                | e0 l0 =>
                    cases sameTail
                | e1 l0 =>
                    exact Or.inr
                      (Exists.intro k0
                        (Exists.intro l0
                          (And.intro rfl (And.intro rfl (BHist.e1.inj sameTail)))))

theorem cont_left_tag_cross_tail_alignment :
    (forall {h k l r : BHist},
      Cont (BHist.e0 h) k (BHist.e1 r) -> Cont (BHist.e0 h) l (BHist.e1 r) ->
        ∃ k0 l0 : BHist, k = BHist.e1 k0 ∧ l = BHist.e1 l0 ∧ hsame k0 l0) ∧
      (forall {h k l r : BHist},
        Cont (BHist.e1 h) k (BHist.e0 r) -> Cont (BHist.e1 h) l (BHist.e0 r) ->
          ∃ k0 l0 : BHist, k = BHist.e0 k0 ∧ l = BHist.e0 l0 ∧ hsame k0 l0) := by
  constructor
  · intro h k l r left right
    have sameTail : hsame k l := cont_left_cancel left right
    have splitLeft := cont_left_tag_cross_result_cases.left left
    cases splitLeft with
    | intro k0 data =>
        cases data with
        | intro kEq _tail =>
            cases kEq
            cases l with
            | Empty =>
                cases sameTail
            | e0 l0 =>
                cases sameTail
            | e1 l0 =>
                exact Exists.intro k0
                  (Exists.intro l0
                    (And.intro rfl (And.intro rfl (BHist.e1.inj sameTail))))
  · intro h k l r left right
    have sameTail : hsame k l := cont_left_cancel left right
    have splitLeft := cont_left_tag_cross_result_cases.right left
    cases splitLeft with
    | intro k0 data =>
        cases data with
        | intro kEq _tail =>
            cases kEq
            cases l with
            | Empty =>
                cases sameTail
            | e0 l0 =>
                exact Exists.intro k0
                  (Exists.intro l0
                    (And.intro rfl (And.intro rfl (BHist.e0.inj sameTail))))
            | e1 l0 =>
                cases sameTail

theorem cont_right_tail_result_cases {h k r : BHist} :
    Cont h k r ->
      (hsame k BHist.Empty ∧ hsame r h) ∨
        (∃ t u : BHist,
          hsame k (BHist.e0 t) ∧ hsame r (BHist.e0 u) ∧ Cont h t u) ∨
          (∃ t u : BHist,
            hsame k (BHist.e1 t) ∧ hsame r (BHist.e1 u) ∧ Cont h t u) := by
  intro hcont
  cases k with
  | Empty =>
      left
      exact And.intro (hsame_refl BHist.Empty) (hcont.trans (append_empty_right h))
  | e0 t =>
      right
      left
      cases cont_step_result_inversions.left hcont with
      | intro u witness =>
          exact Exists.intro t
            (Exists.intro u
              (And.intro (hsame_refl (BHist.e0 t))
                (And.intro witness.left witness.right)))
  | e1 t =>
      right
      right
      cases cont_step_result_inversions.right hcont with
      | intro u witness =>
          exact Exists.intro t
            (Exists.intro u
              (And.intro (hsame_refl (BHist.e1 t))
                (And.intro witness.left witness.right)))

end BEDC.FKernel.Cont
