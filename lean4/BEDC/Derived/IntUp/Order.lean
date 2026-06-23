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

end BEDC.Derived.IntUp
