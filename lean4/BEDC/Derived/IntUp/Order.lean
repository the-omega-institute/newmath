import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (append bwordLength bwordLength_append)

private theorem nat_le_iff_exists_add_right {a b : Nat} :
    a ≤ b ↔ ∃ k : Nat, b = a + k := by
  constructor
  · intro h
    cases Nat.le.dest h with
    | intro k hk =>
        exact ⟨k, hk.symm⟩
  · intro h
    cases h with
    | intro k hk =>
        exact Nat.le.intro hk.symm

def pairLe (x y : BHist × BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧
    BEDC.FKernel.Cont.Cont (append x.1 y.2) tail (append y.1 x.2)

def intLt (x y : BHist × BHist) : Prop :=
  bwordLength x.1 + bwordLength y.2 <
    bwordLength y.1 + bwordLength x.2

def natLeBool : Nat -> Nat -> Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natLeBool a b

theorem natLeBool_true_of_le {a b : Nat} :
    a ≤ b -> natLeBool a b = true := by
  induction a generalizing b with
  | zero =>
      intro _h
      cases b <;> rfl
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact ih (Nat.le_of_succ_le_succ h)

theorem natLeBool_false_of_lt {a b : Nat} :
    b < a -> natLeBool a b = false := by
  induction a generalizing b with
  | zero =>
      intro h
      cases h
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          rfl
      | succ b =>
          exact ih (Nat.succ_lt_succ_iff.mp h)

def intMin (x y : BHist × BHist) : BHist × BHist :=
  if natLeBool
      (bwordLength x.1 + bwordLength y.2)
      (bwordLength y.1 + bwordLength x.2) then x else y

theorem pairLe_reflects_length_order {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    pairLe x y ->
      ∃ k : Nat,
        bwordLength y.1 + bwordLength x.2 =
          bwordLength x.1 + bwordLength y.2 + k := by
  intro hle
  rcases hle with ⟨tail, tailUnary, cont⟩
  refine ⟨bwordLength tail, ?_⟩
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  have sourceUnary : UnaryHistory (append x.1 y.2) := unary_append_closed hx.left hy.right
  have lengthEq := bridge.right.right.right.right sourceUnary tailUnary cont
  rw [bwordLength_append y.1 x.2] at lengthEq
  rw [bwordLength_append x.1 y.2] at lengthEq
  exact lengthEq

theorem pairLe_of_length_order {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    (bwordLength x.1 + bwordLength y.2 ≤ bwordLength y.1 + bwordLength x.2) ->
      pairLe x y := by
  intro hle
  cases nat_le_iff_exists_add_right.mp hle with
  | intro k hk =>
      refine ⟨natToUnary k, natToUnary_unary k, ?_⟩
      apply BEDC.FKernel.Cont.cont_intro
      have lengthEq :
          bwordLength (append (append x.1 y.2) (natToUnary k)) =
            bwordLength (append y.1 x.2) := by
        rw [bwordLength_append (append x.1 y.2) (natToUnary k)]
        rw [bwordLength_append x.1 y.2]
        rw [natToUnary_length k]
        rw [bwordLength_append y.1 x.2]
        exact hk.symm
      exact ((BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
        (unary_append_closed (unary_append_closed hx.left hy.right) (natToUnary_unary k))
        (unary_append_closed hy.left hx.right)).mpr lengthEq).symm

theorem pairLe_iff_length_order {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    pairLe x y ↔
      bwordLength x.1 + bwordLength y.2 ≤ bwordLength y.1 + bwordLength x.2 := by
  constructor
  · intro hle
    exact nat_le_iff_exists_add_right.mpr (pairLe_reflects_length_order hx hy hle)
  · exact pairLe_of_length_order hx hy

theorem pairLe_total {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    pairLe x y ∨ pairLe y x := by
  have leftUnary : UnaryHistory (append x.1 y.2) := unary_append_closed hx.left hy.right
  have rightUnary : UnaryHistory (append y.1 x.2) := unary_append_closed hy.left hx.right
  cases BEDC.Derived.NatUp.NatUnaryPrefix_total leftUnary rightUnary with
  | inl left =>
      exact Or.inl left
  | inr right =>
      exact Or.inr right

theorem intLt_iff_length_lt (x y : BHist × BHist) :
    intLt x y ↔
      bwordLength x.1 + bwordLength y.2 <
        bwordLength y.1 + bwordLength x.2 := by
  rfl

theorem intLt_to_pairLe {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    intLt x y -> pairLe x y := by
  intro hlt
  exact pairLe_of_length_order hx hy (Nat.le_of_lt hlt)

theorem pairLe_antisymm_classifier {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    pairLe x y -> pairLe y x ->
      BEDC.Derived.IntUp.IntPairClassifier x y := by
  intro xy yx
  have xyLen := (pairLe_iff_length_order hx hy).mp xy
  have yxLen := (pairLe_iff_length_order hy hx).mp yx
  have lengthEq :
      bwordLength (append x.1 y.2) = bwordLength (append y.1 x.2) := by
    rw [bwordLength_append x.1 y.2]
    rw [bwordLength_append y.1 x.2]
    exact Nat.le_antisymm xyLen yxLen
  have sourceUnary : UnaryHistory (append x.1 y.2) :=
    unary_append_closed hx.left hy.right
  have targetUnary : UnaryHistory (append y.1 x.2) :=
    unary_append_closed hy.left hx.right
  exact ⟨hx, hy,
    (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
      sourceUnary targetUnary).mpr lengthEq⟩

theorem intMin_carrier {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    BEDC.Derived.IntUp.IntPairCarrier (intMin x y).1 (intMin x y).2 := by
  unfold intMin
  cases natLeBool
      (bwordLength x.1 + bwordLength y.2)
      (bwordLength y.1 + bwordLength x.2) with
  | false => exact hy
  | true => exact hx

theorem intMin_left_classifier_of_le {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    pairLe x y -> BEDC.Derived.IntUp.IntPairClassifier (intMin x y) x := by
  intro xy
  have xyLen := (pairLe_iff_length_order hx hy).mp xy
  have branch :
      natLeBool
        (bwordLength x.1 + bwordLength y.2)
        (bwordLength y.1 + bwordLength x.2) = true :=
    natLeBool_true_of_le xyLen
  unfold intMin
  rw [branch]
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.left hx

theorem intMin_right_classifier_of_not_le {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    (pairLe x y -> False) ->
      BEDC.Derived.IntUp.IntPairClassifier (intMin x y) y := by
  intro notXY
  have notLen :
      ¬ bwordLength x.1 + bwordLength y.2 ≤
        bwordLength y.1 + bwordLength x.2 := by
    intro len
    exact notXY (pairLe_of_length_order hx hy len)
  have branch :
      natLeBool
        (bwordLength x.1 + bwordLength y.2)
        (bwordLength y.1 + bwordLength x.2) = false :=
    natLeBool_false_of_lt (Nat.lt_of_not_ge notLen)
  unfold intMin
  rw [branch]
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.left hy

theorem intMin_left_classifier_of_lt {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    intLt x y -> BEDC.Derived.IntUp.IntPairClassifier (intMin x y) x := by
  intro hlt
  exact intMin_left_classifier_of_le hx hy (intLt_to_pairLe hx hy hlt)

theorem intMin_right_classifier_of_lt {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    intLt y x -> BEDC.Derived.IntUp.IntPairClassifier (intMin x y) y := by
  intro hlt
  have notXY : pairLe x y -> False := by
    intro xy
    have xyLen := (pairLe_iff_length_order hx hy).mp xy
    exact Nat.not_le_of_gt hlt xyLen
  exact intMin_right_classifier_of_not_le hx hy notXY

theorem intMin_spec {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    BEDC.Derived.IntUp.IntPairCarrier (intMin x y).1 (intMin x y).2 ∧
      pairLe (intMin x y) x ∧ pairLe (intMin x y) y ∧
        (BEDC.Derived.IntUp.IntPairClassifier (intMin x y) x ∨
          BEDC.Derived.IntUp.IntPairClassifier (intMin x y) y) := by
  have minCarrier := intMin_carrier hx hy
  unfold intMin at minCarrier ⊢
  by_cases h :
      bwordLength x.1 + bwordLength y.2 ≤
        bwordLength y.1 + bwordLength x.2
  · have branch :
        natLeBool
          (bwordLength x.1 + bwordLength y.2)
          (bwordLength y.1 + bwordLength x.2) = true :=
      natLeBool_true_of_le h
    rw [branch]
    have xy : pairLe x y := pairLe_of_length_order hx hy h
    have xx : pairLe x x := pairLe_of_length_order hx hx (Nat.le_refl _)
    exact ⟨hx, xx,
      xy, Or.inl (IntPairClassifier_equivalence_fields.right.right.left hx)⟩
  · have branch :
        natLeBool
          (bwordLength x.1 + bwordLength y.2)
          (bwordLength y.1 + bwordLength x.2) = false :=
      natLeBool_false_of_lt (Nat.lt_of_not_ge h)
    rw [branch]
    have yxLen :
        bwordLength y.1 + bwordLength x.2 ≤
          bwordLength x.1 + bwordLength y.2 :=
      Nat.le_of_lt (Nat.lt_of_not_ge h)
    have yx : pairLe y x := pairLe_of_length_order hy hx yxLen
    have yy : pairLe y y := pairLe_of_length_order hy hy (Nat.le_refl _)
    exact ⟨hy, yx, yy,
      Or.inr (IntPairClassifier_equivalence_fields.right.right.left hy)⟩

end BEDC.Derived.IntUp
