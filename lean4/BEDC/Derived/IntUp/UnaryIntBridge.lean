import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.NatUp.UnaryNatBridge
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.StdBridge
import BEDC.Derived.IntUp.CanonicalReadback
import BEDC.Derived.IntUp.ZeroRepresentative
import BEDC.Derived.IntUp.Bridge
import BEDC.Derived.IntUp.CommRingCore
import BEDC.Derived.IntUp.Order

namespace BEDC.Derived.IntUp.UnaryIntBridge

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp.UnaryNatBridge
open BEDC.Derived.IntUp

-- BEDC IntUp 的 pair carrier `(p, n)` 表示 `p - n`, 本桥接到 Lean stdlib `Int`.
-- encode 取 unary length 差, 尊重 IntPairClassifier, 且 pairAdd 保持为 `Int.+`; mathlib-free 0-axiom.
def intEncode (p : BHist × BHist) : Int :=
  (unaryLength p.1 : Int) - (unaryLength p.2 : Int)

def intEncodeCore (p : BHist × BHist) : Int :=
  Int.subNatNat (unaryLength p.1) (unaryLength p.2)

def intPairAddEncode (x y : BHist × BHist) : Int :=
  Int.subNatNat (unaryLength x.1 + unaryLength y.1) (unaryLength x.2 + unaryLength y.2)

private theorem subNatNat_succ_succ_pure (m n : Nat) :
    Int.subNatNat (m + 1) (n + 1) = Int.subNatNat m n := by
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
      change Int.subNatNat ((m + k) + 1) ((n + k) + 1) = Int.subNatNat m n
      rw [subNatNat_succ_succ_pure]
      exact ih

private theorem subNatNat_cross_eq_pure {m n p q : Nat}
    (h : m + q = p + n) :
    Int.subNatNat m n = Int.subNatNat p q := by
  rw [← subNatNat_add_add_right_pure m n q]
  rw [h]
  rw [Nat.add_comm n q]
  exact subNatNat_add_add_right_pure p q n

private theorem subNatNat_zero_right_pure : ∀ m : Nat, Int.subNatNat m 0 = Int.ofNat m
  | 0 => rfl
  | m + 1 => by
      unfold Int.subNatNat
      rw [Nat.zero_sub]
      rw [Nat.sub_zero]

private theorem ofNat_sub_ofNat_eq_subNatNat_pure : ∀ m n : Nat,
    ((m : Nat) : Int) - ((n : Nat) : Int) = Int.subNatNat m n
  | 0, 0 => rfl
  | 0, n + 1 => rfl
  | m + 1, 0 => by
      change Int.ofNat (m + 1) = Int.subNatNat (m + 1) 0
      exact (subNatNat_zero_right_pure (m + 1)).symm
  | _ + 1, _ + 1 => by
      rfl

theorem intEncode_eq_core (p : BHist × BHist) :
    intEncode p = intEncodeCore p := by
  cases p with
  | mk pos neg =>
      exact ofNat_sub_ofNat_eq_subNatNat_pure (unaryLength pos) (unaryLength neg)

theorem intEncodeCore_classifier {a b c d : BHist}
    (h : IntPairClassifier (a, b) (c, d)) :
    intEncodeCore (a, b) = intEncodeCore (c, d) := by
  have hlenAppend : unaryLength (append a d) = unaryLength (append c b) :=
    congrArg unaryLength h.right.right
  have hcross : unaryLength a + unaryLength d = unaryLength c + unaryLength b := by
    rw [unaryLength_append a d] at hlenAppend
    rw [unaryLength_append c b] at hlenAppend
    exact hlenAppend
  exact subNatNat_cross_eq_pure hcross

theorem intEncode_classifier {a b c d : BHist}
    (h : IntPairClassifier (a, b) (c, d)) :
    intEncode (a, b) = intEncode (c, d) := by
  rw [intEncode_eq_core (a, b)]
  rw [intEncode_eq_core (c, d)]
  exact intEncodeCore_classifier h

theorem intEncodeCore_pairAdd (x y : BHist × BHist) :
    intEncodeCore (pairAdd x y) = intPairAddEncode x y := by
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          unfold intEncodeCore intPairAddEncode pairAdd
          rw [unaryLength_append xp yp]
          rw [unaryLength_append xn yn]

theorem intEncode_pairAdd (x y : BHist × BHist) :
    intEncode (pairAdd x y) = intPairAddEncode x y := by
  rw [intEncode_eq_core (pairAdd x y)]
  exact intEncodeCore_pairAdd x y

end BEDC.Derived.IntUp.UnaryIntBridge
