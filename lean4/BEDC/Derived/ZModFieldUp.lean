import BEDC.Derived.ZModUp
import BEDC.Derived.PadicUp.PrimeInverse

namespace BEDC.Derived.ZModFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.ZModUp

def zmodNonzero {p : BHist} (x : ZMod p) : Prop :=
  hsame x.val BHist.Empty -> False

def zmodInv {p : BHist} (prime : NatPrime p) (x : ZMod p)
    (hx : zmodNonzero x) : ZMod p :=
  invModPrime prime x hx

theorem zmodInv_mul {p : BHist} (prime : NatPrime p) (x : ZMod p)
    (hx : zmodNonzero x) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime) x
        (zmodInv prime x hx))
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  exact invModPrime_spec prime x hx

theorem zmodMul_inv {p : BHist} (prime : NatPrime p) (x : ZMod p)
    (hx : zmodNonzero x) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodInv prime x hx) x)
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  exact zmodEq_trans
    (zmodMul_comm prime.left (NatPrime_empty_absurd prime)
      (zmodInv prime x hx) x)
    (zmodInv_mul prime x hx)

theorem zmodOne_nonzero {p : BHist} (prime : NatPrime p) :
    zmodNonzero (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  intro oneEmpty
  have oneStrict :
      hsame (natModFn p NatOne) NatOne := by
    exact natModFn_of_strict prime.left (NatPrime_empty_absurd prime)
      (unary_e1_closed unary_empty) prime.right.left
  exact not_hsame_e1_empty (hsame_trans (hsame_symm oneStrict) oneEmpty)

theorem zmodNonzero_respects {p : BHist} {x y : ZMod p} :
    zmodEq x y -> zmodNonzero x -> zmodNonzero y := by
  intro same hx yEmpty
  exact hx (hsame_trans same yEmpty)

theorem zmodInv_congr {p : BHist} (prime : NatPrime p)
    {x y : ZMod p} (same : zmodEq x y)
    (hx : zmodNonzero x) (hy : zmodNonzero y) :
    zmodEq (zmodInv prime x hx) (zmodInv prime y hy) := by
  have leftUnit :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodInv prime x hx) y)
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
    exact zmodEq_trans
      (zmodEq_symm
        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (hsame_refl _) same))
      (zmodMul_inv prime x hx)
  have rightUnit :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) y
          (zmodInv prime y hy))
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
    zmodInv_mul prime y hy
  have reassociate :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodMul p prime.left (NatPrime_empty_absurd prime)
            (zmodInv prime x hx) y)
          (zmodInv prime y hy))
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodInv prime x hx)
          (zmodMul p prime.left (NatPrime_empty_absurd prime) y
            (zmodInv prime y hy))) := by
    exact zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
      (zmodInv prime x hx) y (zmodInv prime y hy)
  have leftReduce :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodMul p prime.left (NatPrime_empty_absurd prime)
            (zmodInv prime x hx) y)
          (zmodInv prime y hy))
        (zmodInv prime y hy) := by
    exact zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        leftUnit (zmodEq_refl (zmodInv prime y hy)))
      (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
        (zmodInv prime y hy))
  have rightReduce :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodInv prime x hx)
          (zmodMul p prime.left (NatPrime_empty_absurd prime) y
            (zmodInv prime y hy)))
        (zmodInv prime x hx) := by
    exact zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodEq_refl (zmodInv prime x hx)) rightUnit)
      (zmodOne_mul_right prime.left (NatPrime_empty_absurd prime)
        (zmodInv prime x hx))
  exact zmodEq_trans (zmodEq_symm rightReduce)
    (zmodEq_trans (zmodEq_symm reassociate) leftReduce)

structure ZModFieldCore (p : BHist) extends ZModCommRingCore p where
  prime : NatPrime p
  nonzero : carrier -> Prop
  nonzero_respects : ∀ {x y : carrier}, eqv x y -> nonzero x -> nonzero y
  one_nonzero : nonzero one
  inv : (x : carrier) -> nonzero x -> carrier
  mul_inv : ∀ (x : carrier) (hx : nonzero x), eqv (mul x (inv x hx)) one
  inv_mul : ∀ (x : carrier) (hx : nonzero x), eqv (mul (inv x hx) x) one
  inv_respects : ∀ {x y : carrier}, eqv x y ->
    ∀ (hx : nonzero x) (hy : nonzero y), eqv (inv x hx) (inv y hy)

def zmodFieldCore (p : BHist) (prime : NatPrime p) : ZModFieldCore p :=
  { zmodCommRingCore p prime.left (NatPrime_empty_absurd prime) with
    prime := prime
    nonzero := zmodNonzero
    nonzero_respects := zmodNonzero_respects
    one_nonzero := zmodOne_nonzero prime
    inv := zmodInv prime
    mul_inv := zmodInv_mul prime
    inv_mul := zmodMul_inv prime
    inv_respects := zmodInv_congr prime }

end BEDC.Derived.ZModFieldUp
