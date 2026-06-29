import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.UnaryIntBridge
-- BEDC IntUp 乘法桥: carrier-correct 的 `intEncode_pairMul` 把 `pairMul` 接到
-- Lean `Int.*`, 配合 `UnaryIntBridge` 的加法完成整数环结构；无约束反例记录边界。
-- 本文件保持 mathlib-free 与 0-axiom。

namespace BEDC.Derived.IntUp.UnaryIntMulBridge

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (append)
open BEDC.Derived.NatUp.UnaryNatBridge
open BEDC.Derived.IntUp
open BEDC.Derived.IntUp.UnaryIntBridge

private theorem unaryLength_natMulFn {d q : BHist}
    (_hd : UnaryHistory d) (hq : UnaryHistory q) :
    unaryLength (natMulFn d q) = unaryLength d * unaryLength q := by
  induction q with
  | Empty =>
      exact (Nat.mul_zero (unaryLength d)).symm
  | e0 _ =>
      cases hq
  | e1 q ih =>
      change unaryLength (append (natMulFn d q) d) =
        unaryLength d * (unaryLength q + 1)
      rw [unaryLength_append]
      rw [ih hq]
      exact (Nat.mul_succ (unaryLength d) (unaryLength q)).symm

private theorem subNatNat_succ_succ_pure (m n : Nat) :
    Int.subNatNat (Nat.succ m) (Nat.succ n) = Int.subNatNat m n := by
  unfold Int.subNatNat
  rw [Nat.succ_sub_succ_eq_sub]
  rw [Nat.succ_sub_succ_eq_sub]

private theorem subNatNat_add_add_right_pure (m n k : Nat) :
    Int.subNatNat (m + k) (n + k) = Int.subNatNat m n := by
  induction k with
  | zero =>
      rw [Nat.add_zero]
      rw [Nat.add_zero]
  | succ k ih =>
      change Int.subNatNat (Nat.succ (m + k)) (Nat.succ (n + k)) =
        Int.subNatNat m n
      rw [subNatNat_succ_succ_pure]
      exact ih

private theorem subNatNat_zero_right_pure : ∀ m : Nat, Int.subNatNat m 0 = Int.ofNat m
  | 0 => rfl
  | Nat.succ m => by
      unfold Int.subNatNat
      rw [Nat.zero_sub]
      rw [Nat.sub_zero]

private theorem subNatNat_zero_left_pure : ∀ n : Nat, Int.subNatNat 0 n = Int.negOfNat n
  | 0 => rfl
  | Nat.succ _ => rfl

private theorem ofNat_sub_ofNat_eq_subNatNat_pure : ∀ m n : Nat,
    ((m : Nat) : Int) - ((n : Nat) : Int) = Int.subNatNat m n
  | 0, 0 => rfl
  | 0, Nat.succ _ => rfl
  | Nat.succ m, 0 => by
      change Int.ofNat (Nat.succ m) = Int.subNatNat (Nat.succ m) 0
      exact (subNatNat_zero_right_pure (Nat.succ m)).symm
  | Nat.succ _, Nat.succ _ => by
      rfl

private theorem nat_add_four_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) :=
      congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) :=
      congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) :=
      congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private theorem nat_succ_mul_pair_repack (a b c d : Nat) :
    Nat.succ a * c + Nat.succ b * d = (a * c + b * d) + (c + d) := by
  calc
    Nat.succ a * c + Nat.succ b * d = (a * c + c) + (b * d + d) := by
      rw [Nat.succ_mul]
      rw [Nat.succ_mul]
    _ = (a * c + b * d) + (c + d) := nat_add_four_swap (a * c) c (b * d) d

private theorem ofNat_mul_subNatNat_pure : ∀ a c d : Nat,
    Int.ofNat a * Int.subNatNat c d = Int.subNatNat (a * c) (a * d)
  | a, 0, 0 => by
      change Int.ofNat (a * 0) = Int.ofNat 0
      rw [Nat.mul_zero]
  | a, Nat.succ c, 0 => by
      rw [subNatNat_zero_right_pure (Nat.succ c)]
      rw [Nat.mul_zero]
      rw [subNatNat_zero_right_pure (a * Nat.succ c)]
      exact Int.ofNat_mul_ofNat a (Nat.succ c)
  | a, 0, Nat.succ d => by
      rw [Nat.mul_zero]
      rw [subNatNat_zero_left_pure (a * Nat.succ d)]
      cases a with
      | zero =>
          rfl
      | succ a =>
          rfl
  | a, Nat.succ c, Nat.succ d => by
      rw [subNatNat_succ_succ_pure c d]
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [subNatNat_add_add_right_pure (a * c) (a * d) a]
      exact ofNat_mul_subNatNat_pure a c d

private theorem zero_mul_int_pure : ∀ z : Int, (0 : Int) * z = 0
  | Int.ofNat n => by
      change Int.ofNat (0 * n) = (0 : Int)
      rw [Nat.zero_mul]
      rfl
  | Int.negSucc n => by
      change Int.negOfNat (0 * Nat.succ n) = (0 : Int)
      rw [Nat.zero_mul]
      rfl

private theorem negOfNat_mul_ofNat_pure : ∀ a b : Nat,
    Int.negOfNat a * Int.ofNat b = Int.negOfNat (a * b)
  | 0, b => by
      rw [Nat.zero_mul]
      change (0 : Int) * Int.ofNat b = 0
      exact zero_mul_int_pure (Int.ofNat b)
  | Nat.succ _, _ => by
      rfl

private theorem negOfNat_mul_negOfNat_pure : ∀ a b : Nat,
    Int.negOfNat a * Int.negOfNat b = Int.ofNat (a * b)
  | 0, b => by
      rw [Nat.zero_mul]
      change (0 : Int) * Int.negOfNat b = 0
      exact zero_mul_int_pure (Int.negOfNat b)
  | Nat.succ a, 0 => by
      rw [Nat.mul_zero]
      rfl
  | Nat.succ _, Nat.succ _ => by
      rfl

private theorem negOfNat_mul_subNatNat_pure : ∀ a c d : Nat,
    Int.negOfNat a * Int.subNatNat c d = Int.subNatNat (a * d) (a * c)
  | a, 0, 0 => by
      change Int.negOfNat a * Int.ofNat 0 = Int.ofNat 0
      rw [negOfNat_mul_ofNat_pure]
      rw [Nat.mul_zero]
      rfl
  | a, Nat.succ c, 0 => by
      rw [Nat.mul_zero]
      rw [subNatNat_zero_left_pure (a * Nat.succ c)]
      rw [subNatNat_zero_right_pure (Nat.succ c)]
      exact negOfNat_mul_ofNat_pure a (Nat.succ c)
  | a, 0, Nat.succ d => by
      rw [Nat.mul_zero]
      rw [subNatNat_zero_right_pure (a * Nat.succ d)]
      rw [subNatNat_zero_left_pure (Nat.succ d)]
      exact negOfNat_mul_negOfNat_pure a (Nat.succ d)
  | a, Nat.succ c, Nat.succ d => by
      rw [subNatNat_succ_succ_pure c d]
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [subNatNat_add_add_right_pure (a * d) (a * c) a]
      exact negOfNat_mul_subNatNat_pure a c d

private theorem subNatNat_mul_subNatNat_pure : ∀ a b c d : Nat,
    Int.subNatNat a b * Int.subNatNat c d =
      Int.subNatNat (a * c + b * d) (a * d + b * c)
  | 0, 0, c, d => by
      change Int.ofNat 0 * Int.subNatNat c d =
        Int.subNatNat (0 * c + 0 * d) (0 * d + 0 * c)
      rw [ofNat_mul_subNatNat_pure 0 c d]
      rw [Nat.zero_mul]
      rw [Nat.zero_mul]
  | Nat.succ a, 0, c, d => by
      rw [subNatNat_zero_right_pure (Nat.succ a)]
      rw [ofNat_mul_subNatNat_pure (Nat.succ a) c d]
      rw [Nat.zero_mul]
      rw [Nat.zero_mul]
      rw [Nat.add_zero]
      rw [Nat.add_zero]
  | 0, Nat.succ b, c, d => by
      rw [subNatNat_zero_left_pure (Nat.succ b)]
      rw [negOfNat_mul_subNatNat_pure (Nat.succ b) c d]
      rw [Nat.zero_mul]
      rw [Nat.zero_mul]
      rw [Nat.zero_add]
      rw [Nat.zero_add]
  | Nat.succ a, Nat.succ b, c, d => by
      rw [subNatNat_succ_succ_pure a b]
      rw [nat_succ_mul_pair_repack a b c d]
      rw [nat_succ_mul_pair_repack a b d c]
      rw [Nat.add_comm d c]
      rw [subNatNat_add_add_right_pure (a * c + b * d) (a * d + b * c) (c + d)]
      exact subNatNat_mul_subNatNat_pure a b c d

private theorem intEncodeCore_pairMul (x y : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    intEncodeCore (pairMul x y) =
      Int.subNatNat
        (unaryLength x.1 * unaryLength y.1 + unaryLength x.2 * unaryLength y.2)
        (unaryLength x.1 * unaryLength y.2 + unaryLength x.2 * unaryLength y.1) := by
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          unfold intEncodeCore pairMul
          rw [unaryLength_append]
          rw [unaryLength_append]
          rw [unaryLength_natMulFn hx.left hy.left]
          rw [unaryLength_natMulFn hx.right hy.right]
          rw [unaryLength_natMulFn hx.left hy.right]
          rw [unaryLength_natMulFn hx.right hy.left]

theorem intEncode_pairMul (x y : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    intEncode (pairMul x y) = intEncode x * intEncode y := by
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          rw [intEncode_eq_core (pairMul (xp, xn) (yp, yn))]
          rw [intEncode_eq_core (xp, xn)]
          rw [intEncode_eq_core (yp, yn)]
          rw [intEncodeCore_pairMul (xp, xn) (yp, yn) hx hy]
          unfold intEncodeCore
          exact (subNatNat_mul_subNatNat_pure
            (unaryLength xp) (unaryLength xn) (unaryLength yp) (unaryLength yn)).symm

def unrestrictedCounterexampleX : BHist × BHist :=
  (BHist.e1 BHist.Empty, BHist.Empty)

def unrestrictedCounterexampleY : BHist × BHist :=
  (BHist.e0 (BHist.e1 BHist.Empty), BHist.Empty)

theorem intEncode_pairMul_unrestricted_false :
    intEncode (pairMul unrestrictedCounterexampleX unrestrictedCounterexampleY) ≠
      intEncode unrestrictedCounterexampleX * intEncode unrestrictedCounterexampleY := by
  unfold unrestrictedCounterexampleX unrestrictedCounterexampleY
  unfold intEncode pairMul natMulFn unaryLength
  decide

end BEDC.Derived.IntUp.UnaryIntMulBridge
