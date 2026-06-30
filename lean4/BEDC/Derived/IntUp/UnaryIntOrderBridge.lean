import BEDC.Derived.IntUp.UnaryIntBridge

-- BEDC IntUp negation/order 桥：`intEncode_pairNeg` 连接 `pairNeg` 与 Lean `Int` 负号，
-- `intEncode_le` 在 carrier-correct 条件下连接 `pairLe` 与 Lean `Int.≤`。
-- 配合 `UnaryIntBridge` 与 `UnaryIntMulBridge` 完成 `IntPairCarrier ≃ Lean Int`
-- 的有序环 `+/*/-/≤` 保结构桥；mathlib-free、0-axiom。

namespace BEDC.Derived.IntUp.UnaryIntOrderBridge

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp.UnaryNatBridge
open BEDC.Derived.IntUp
open BEDC.Derived.IntUp.UnaryIntBridge

private theorem unaryLength_eq_bwordLength {h : BHist} (hh : UnaryHistory h) :
    unaryLength h = bwordLength h := by
  induction h with
  | Empty =>
      rfl
  | e0 h =>
      cases hh
  | e1 h ih =>
      change unaryLength h + 1 = bwordLength h + 1
      exact congrArg (fun n => n + 1) (ih hh)

private theorem bwordLength_eq_unaryLength {h : BHist} (hh : UnaryHistory h) :
    bwordLength h = unaryLength h :=
  (unaryLength_eq_bwordLength hh).symm

private theorem subNatNat_succ_succ_pure (m n : Nat) :
    Int.subNatNat (m + 1) (n + 1) = Int.subNatNat m n := by
  unfold Int.subNatNat
  rw [Nat.succ_sub_succ_eq_sub]
  rw [Nat.succ_sub_succ_eq_sub]

private theorem subNatNat_zero_right_pure : ∀ m : Nat, Int.subNatNat m 0 = Int.ofNat m
  | 0 => rfl
  | m + 1 => by
      unfold Int.subNatNat
      rw [Nat.zero_sub]
      rw [Nat.sub_zero]

private theorem subNatNat_zero_left_pure : ∀ n : Nat, Int.subNatNat 0 n = Int.negOfNat n
  | 0 => rfl
  | _ + 1 => rfl

private theorem subNatNat_swap_neg_pure : ∀ m n : Nat,
    Int.subNatNat n m = -Int.subNatNat m n
  | 0, 0 => rfl
  | 0, n + 1 => by
      rw [subNatNat_zero_right_pure (n + 1)]
      rw [subNatNat_zero_left_pure (n + 1)]
      rfl
  | m + 1, 0 => by
      rw [subNatNat_zero_left_pure (m + 1)]
      rw [subNatNat_zero_right_pure (m + 1)]
      rfl
  | m + 1, n + 1 => by
      rw [subNatNat_succ_succ_pure n m]
      rw [subNatNat_succ_succ_pure m n]
      exact subNatNat_swap_neg_pure m n

private theorem int_zero_add_pure : ∀ z : Int, (0 : Int) + z = z
  | Int.ofNat n => by
      change Int.ofNat (0 + n) = Int.ofNat n
      rw [Nat.zero_add]
  | Int.negSucc _ => rfl

private theorem int_add_zero_pure : ∀ z : Int, z + (0 : Int) = z
  | Int.ofNat n => by
      change Int.ofNat (n + 0) = Int.ofNat n
      rw [Nat.add_zero]
  | Int.negSucc _ => rfl

private theorem ofNat_add_subNatNat_pure : ∀ a c d : Nat,
    Int.ofNat a + Int.subNatNat c d = Int.subNatNat (a + c) d
  | a, 0, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_right_pure a]
      exact int_add_zero_pure (Int.ofNat a)
  | a, c + 1, 0 => by
      rw [subNatNat_zero_right_pure (c + 1)]
      rw [subNatNat_zero_right_pure (a + (c + 1))]
      exact Int.ofNat_add_ofNat a (c + 1)
  | a, 0, d + 1 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_left_pure (d + 1)]
      rfl
  | a, c + 1, d + 1 => by
      rw [subNatNat_succ_succ_pure c d]
      rw [Nat.add_succ]
      rw [subNatNat_succ_succ_pure (a + c) d]
      exact ofNat_add_subNatNat_pure a c d

private theorem negOfNat_add_subNatNat_pure : ∀ b c d : Nat,
    Int.negOfNat b + Int.subNatNat c d = Int.subNatNat c (b + d)
  | 0, c, d => by
      rw [Nat.zero_add]
      change (0 : Int) + Int.subNatNat c d = Int.subNatNat c d
      exact int_zero_add_pure (Int.subNatNat c d)
  | b + 1, 0, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_left_pure (b + 1)]
      exact int_add_zero_pure (Int.negOfNat (b + 1))
  | b + 1, c + 1, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_right_pure (c + 1)]
      rfl
  | b + 1, 0, d + 1 => by
      rw [subNatNat_zero_left_pure (b + 1 + (d + 1))]
      rw [subNatNat_zero_left_pure (d + 1)]
      rw [Nat.add_succ]
      exact Int.negOfNat_add (b + 1) (d + 1)
  | b + 1, c + 1, d + 1 => by
      rw [subNatNat_succ_succ_pure c d]
      rw [Nat.add_succ]
      change Int.negOfNat (b + 1) + Int.subNatNat c d =
        Int.subNatNat (c + 1) ((b + 1 + d) + 1)
      rw [subNatNat_succ_succ_pure c (b + 1 + d)]
      exact negOfNat_add_subNatNat_pure (b + 1) c d

private theorem subNatNat_add_subNatNat_pure : ∀ a b c d : Nat,
    Int.subNatNat a b + Int.subNatNat c d =
      Int.subNatNat (a + c) (b + d)
  | 0, 0, c, d => by
      rw [Nat.zero_add]
      rw [Nat.zero_add]
      change (0 : Int) + Int.subNatNat c d = Int.subNatNat c d
      exact int_zero_add_pure (Int.subNatNat c d)
  | a + 1, 0, c, d => by
      rw [subNatNat_zero_right_pure (a + 1)]
      rw [Nat.zero_add]
      exact ofNat_add_subNatNat_pure (a + 1) c d
  | 0, b + 1, c, d => by
      rw [subNatNat_zero_left_pure (b + 1)]
      rw [Nat.zero_add]
      exact negOfNat_add_subNatNat_pure (b + 1) c d
  | a + 1, b + 1, c, d => by
      rw [subNatNat_succ_succ_pure a b]
      rw [Nat.succ_add]
      rw [Nat.succ_add]
      rw [subNatNat_succ_succ_pure (a + c) (b + d)]
      exact subNatNat_add_subNatNat_pure a b c d

private theorem subNatNat_sub_subNatNat_pure (a b c d : Nat) :
    Int.subNatNat c d - Int.subNatNat a b = Int.subNatNat (c + b) (d + a) := by
  change Int.subNatNat c d + (-Int.subNatNat a b) = Int.subNatNat (c + b) (d + a)
  rw [← subNatNat_swap_neg_pure a b]
  exact subNatNat_add_subNatNat_pure c d b a

private theorem subNatNat_add_left_pure : ∀ n k : Nat,
    Int.subNatNat (n + k) n = Int.ofNat k
  | 0, k => by
      rw [Nat.zero_add]
      exact subNatNat_zero_right_pure k
  | n + 1, k => by
      rw [Nat.succ_add]
      rw [subNatNat_succ_succ_pure (n + k) n]
      exact subNatNat_add_left_pure n k

private theorem subNatNat_nonneg_of_le_pure {m n : Nat} (h : n ≤ m) :
    Int.NonNeg (Int.subNatNat m n) := by
  cases Nat.le.dest h with
  | intro k hk =>
      rw [← hk]
      rw [subNatNat_add_left_pure n k]
      exact Int.NonNeg.mk k

private theorem le_of_subNatNat_nonneg_pure {m n : Nat}
    (h : Int.NonNeg (Int.subNatNat m n)) :
    n ≤ m := by
  unfold Int.subNatNat at h
  cases hsub : n - m with
  | zero =>
      exact Nat.le_of_sub_eq_zero hsub
  | succ k =>
      rw [hsub] at h
      cases h

private theorem ofNat_sub_ofNat_eq_subNatNat_pure : ∀ m n : Nat,
    ((m : Nat) : Int) - ((n : Nat) : Int) = Int.subNatNat m n
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | m + 1, 0 => by
      change Int.ofNat (m + 1) = Int.subNatNat (m + 1) 0
      exact (subNatNat_zero_right_pure (m + 1)).symm
  | _ + 1, _ + 1 => by
      rfl

theorem intEncode_pairNeg (x : BHist × BHist) :
    intEncode (pairNeg x) = -intEncode x := by
  cases x with
  | mk p n =>
      rw [intEncode_eq_core (pairNeg (p, n))]
      rw [intEncode_eq_core (p, n)]
      unfold intEncodeCore pairNeg
      exact subNatNat_swap_neg_pure (unaryLength p) (unaryLength n)

private theorem pairLe_iff_unary_length_order {x y : BHist × BHist}
    (hx : IntPairCarrier x.1 x.2)
    (hy : IntPairCarrier y.1 y.2) :
    pairLe x y ↔ unaryLength x.1 + unaryLength y.2 ≤ unaryLength y.1 + unaryLength x.2 := by
  rw [pairLe_iff_length_order hx hy]
  rw [bwordLength_eq_unaryLength hx.left]
  rw [bwordLength_eq_unaryLength hx.right]
  rw [bwordLength_eq_unaryLength hy.left]
  rw [bwordLength_eq_unaryLength hy.right]

theorem intEncode_le {x y : BHist × BHist}
    (hx : IntPairCarrier x.1 x.2)
    (hy : IntPairCarrier y.1 y.2) :
    pairLe x y ↔ intEncode x ≤ intEncode y := by
  constructor
  · intro hle
    cases x with
    | mk xp xn =>
        cases y with
        | mk yp yn =>
            have hBWord :
                bwordLength xp + bwordLength yn ≤ bwordLength yp + bwordLength xn := by
              cases pairLe_reflects_length_order hx hy hle with
              | intro k hk =>
                  exact Nat.le.intro hk.symm
            have hNat :
                unaryLength xp + unaryLength yn ≤ unaryLength yp + unaryLength xn := by
              rw [bwordLength_eq_unaryLength hx.left] at hBWord
              rw [bwordLength_eq_unaryLength hx.right] at hBWord
              rw [bwordLength_eq_unaryLength hy.left] at hBWord
              rw [bwordLength_eq_unaryLength hy.right] at hBWord
              exact hBWord
            unfold intEncode
            unfold LE.le Int.instLEInt Int.le
            rw [ofNat_sub_ofNat_eq_subNatNat_pure (unaryLength yp) (unaryLength yn)]
            rw [ofNat_sub_ofNat_eq_subNatNat_pure (unaryLength xp) (unaryLength xn)]
            change Int.NonNeg
              (Int.subNatNat (unaryLength yp) (unaryLength yn) -
                Int.subNatNat (unaryLength xp) (unaryLength xn))
            rw [subNatNat_sub_subNatNat_pure
              (unaryLength xp) (unaryLength xn) (unaryLength yp) (unaryLength yn)]
            rw [Nat.add_comm (unaryLength yn) (unaryLength xp)]
            exact subNatNat_nonneg_of_le_pure hNat
  · intro hle
    cases x with
    | mk xp xn =>
        cases y with
        | mk yp yn =>
            have hNat :
                unaryLength xp + unaryLength yn ≤ unaryLength yp + unaryLength xn := by
              unfold intEncode at hle
              unfold LE.le Int.instLEInt Int.le at hle
              rw [ofNat_sub_ofNat_eq_subNatNat_pure (unaryLength yp) (unaryLength yn)] at hle
              rw [ofNat_sub_ofNat_eq_subNatNat_pure (unaryLength xp) (unaryLength xn)] at hle
              change Int.NonNeg
                (Int.subNatNat (unaryLength yp) (unaryLength yn) -
                  Int.subNatNat (unaryLength xp) (unaryLength xn)) at hle
              rw [subNatNat_sub_subNatNat_pure
                (unaryLength xp) (unaryLength xn) (unaryLength yp) (unaryLength yn)] at hle
              rw [Nat.add_comm (unaryLength yn) (unaryLength xp)] at hle
              exact le_of_subNatNat_nonneg_pure hle
            have hBWord :
                bwordLength xp + bwordLength yn ≤ bwordLength yp + bwordLength xn := by
              rw [bwordLength_eq_unaryLength hx.left]
              rw [bwordLength_eq_unaryLength hx.right]
              rw [bwordLength_eq_unaryLength hy.left]
              rw [bwordLength_eq_unaryLength hy.right]
              exact hNat
            exact pairLe_of_length_order hx hy hBWord

end BEDC.Derived.IntUp.UnaryIntOrderBridge
