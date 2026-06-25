import BEDC.Derived.ZModFieldUp
import BEDC.Derived.LegendreUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.GcdUp

namespace BEDC.Derived.FermatWilsonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp

/-!
本文件导出 `ZMod p` 上通往 Fermat/Wilson 路线的乘法核心：
幂、非零幂、cancellation，以及非零剩余类左乘的显式逆映射。
-/

def zmodPow {p : BHist} (prime : NatPrime p) (x : ZMod p) : BHist -> ZMod p
  | BHist.Empty => zmodOne p prime.left (NatPrime_empty_absurd prime)
  | BHist.e0 _ => zmodOne p prime.left (NatPrime_empty_absurd prime)
  | BHist.e1 n =>
      zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodPow prime x n) x

theorem zmodPow_empty {p : BHist} (prime : NatPrime p) (x : ZMod p) :
    zmodEq (zmodPow prime x BHist.Empty)
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  rfl

theorem zmodPow_succ {p e : BHist} (prime : NatPrime p) (x : ZMod p) :
    zmodEq (zmodPow prime x (BHist.e1 e))
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodPow prime x e) x) := by
  rfl

theorem zmodPow_congr {p e : BHist} (prime : NatPrime p)
    {x y : ZMod p} :
    UnaryHistory e -> zmodEq x y ->
      zmodEq (zmodPow prime x e) (zmodPow prime y e) := by
  intro eUnary sameXY
  induction e with
  | Empty =>
      rfl
  | e0 eTail _ih =>
      cases eUnary
  | e1 eTail ih =>
      exact zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (ih (unary_e1_inversion eUnary)) sameXY

theorem zmodPow_nonzero {p e : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    UnaryHistory e -> zmodNonzero x -> zmodNonzero (zmodPow prime x e) := by
  intro eUnary xNonzero
  induction e with
  | Empty =>
      exact zmodOne_nonzero prime
  | e0 eTail _ih =>
      cases eUnary
  | e1 eTail ih =>
      exact BEDC.Derived.LegendreUp.zmodMul_nonzero prime
        (ih (unary_e1_inversion eUnary)) xNonzero

theorem zmodMul_right_cancel_nonzero {p : BHist} (prime : NatPrime p)
    {a b c : ZMod p} :
    zmodNonzero c ->
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) a c)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) b c) ->
        zmodEq a b := by
  intro cNonzero sameProduct
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  let invC := zmodInv prime c cNonzero
  have multiplied :
      zmodEq (mul (mul a c) invC) (mul (mul b c) invC) :=
    zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      sameProduct (zmodEq_refl invC)
  have leftReduce : zmodEq (mul (mul a c) invC) a :=
    zmodEq_trans
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime) a c invC)
      (zmodEq_trans
        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (zmodEq_refl a) (zmodInv_mul prime c cNonzero))
        (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime) a))
  have rightReduce : zmodEq (mul (mul b c) invC) b :=
    zmodEq_trans
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime) b c invC)
      (zmodEq_trans
        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (zmodEq_refl b) (zmodInv_mul prime c cNonzero))
        (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime) b))
  exact zmodEq_trans (zmodEq_symm leftReduce)
    (zmodEq_trans multiplied rightReduce)

theorem zmodMul_left_cancel_nonzero {p : BHist} (prime : NatPrime p)
    {a b c : ZMod p} :
    zmodNonzero c ->
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) c a)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) c b) ->
        zmodEq a b := by
  intro cNonzero sameProduct
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  have rightProduct : zmodEq (mul a c) (mul b c) :=
    zmodEq_trans
      (zmodMul_comm prime.left (NatPrime_empty_absurd prime) a c)
      (zmodEq_trans sameProduct
        (zmodEq_symm
          (zmodMul_comm prime.left (NatPrime_empty_absurd prime) b c)))
  exact zmodMul_right_cancel_nonzero prime cNonzero rightProduct

def zmodUnitMul {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (_aNonzero : zmodNonzero a) (x : ZMod p) : ZMod p :=
  zmodMul p prime.left (NatPrime_empty_absurd prime) a x

def zmodUnitDiv {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (x : ZMod p) : ZMod p :=
  zmodMul p prime.left (NatPrime_empty_absurd prime)
    (zmodInv prime a aNonzero) x

theorem zmodUnitDiv_unitMul {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (x : ZMod p) :
    zmodEq
      (zmodUnitDiv prime a aNonzero
        (zmodUnitMul prime a aNonzero x))
      x := by
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  exact zmodEq_trans
    (zmodEq_symm
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
        (zmodInv prime a aNonzero) a x))
    (zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodMul_inv prime a aNonzero) (zmodEq_refl x))
      (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime) x))

theorem zmodUnitMul_unitDiv {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (x : ZMod p) :
    zmodEq
      (zmodUnitMul prime a aNonzero
        (zmodUnitDiv prime a aNonzero x))
      x := by
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  exact zmodEq_trans
    (zmodEq_symm
      (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
        a (zmodInv prime a aNonzero) x))
    (zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodInv_mul prime a aNonzero) (zmodEq_refl x))
      (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime) x))

theorem zmodUnitMul_nonzero {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) {x : ZMod p} :
    zmodNonzero x -> zmodNonzero (zmodUnitMul prime a aNonzero x) := by
  intro xNonzero
  exact BEDC.Derived.LegendreUp.zmodMul_nonzero prime aNonzero xNonzero

end BEDC.Derived.FermatWilsonUp
