import BEDC.Algebra.Rel.RingEquiv
import BEDC.Derived.FermatLittleUp

namespace BEDC.Derived.FrobeniusUp

open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.FermatLittleUp

def frobenius {p : BHist} (prime : NatPrime p) (x : ZMod p) : ZMod p :=
  zmodPowNat prime x (bwordLength p)

theorem frobenius_respects {p : BHist} (prime : NatPrime p)
    {x y : ZMod p} :
    zmodEq x y -> zmodEq (frobenius prime x) (frobenius prime y) := by
  intro same
  unfold frobenius
  induction bwordLength p with
  | zero =>
      rfl
  | succ k ih =>
      exact zmodMul_congr prime.left (NatPrime_empty_absurd prime) ih same

theorem frobenius_id {p : BHist} (prime : NatPrime p) (x : ZMod p) :
    zmodEq (frobenius prime x) x := by
  let fromNat : ZMod p :=
    zmodFromNat p prime.left (NatPrime_empty_absurd prime) x.val
      (zmodVal_unary prime.left x)
  have fromNatSame : zmodEq fromNat x := by
    change hsame (natModFn p x.val) x.val
    exact natModFn_of_strict prime.left (NatPrime_empty_absurd prime)
      (zmodVal_unary prime.left x) x.isLt
  have powLift :
      zmodEq (frobenius prime x) (frobenius prime fromNat) :=
    frobenius_respects prime (zmodEq_symm fromNatSame)
  have fermatAtRepresentative :
      zmodEq (frobenius prime fromNat) fromNat := by
    unfold frobenius fromNat
    exact fermatLittle_all prime (zmodVal_unary prime.left x)
  exact zmodEq_trans powLift
    (zmodEq_trans fermatAtRepresentative fromNatSame)

theorem frobenius_zero {p : BHist} (prime : NatPrime p) :
    zmodEq
      (frobenius prime (zmodZero p prime.left (NatPrime_empty_absurd prime)))
      (zmodZero p prime.left (NatPrime_empty_absurd prime)) :=
  frobenius_id prime (zmodZero p prime.left (NatPrime_empty_absurd prime))

theorem frobenius_one {p : BHist} (prime : NatPrime p) :
    zmodEq
      (frobenius prime (zmodOne p prime.left (NatPrime_empty_absurd prime)))
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
  frobenius_id prime (zmodOne p prime.left (NatPrime_empty_absurd prime))

theorem frobenius_freshmanDream {p : BHist} (prime : NatPrime p)
    (x y : ZMod p) :
    zmodEq
      (frobenius prime
        (zmodAdd p prime.left (NatPrime_empty_absurd prime) x y))
      (zmodAdd p prime.left (NatPrime_empty_absurd prime)
        (frobenius prime x) (frobenius prime y)) := by
  have leftId :
      zmodEq
        (frobenius prime
          (zmodAdd p prime.left (NatPrime_empty_absurd prime) x y))
        (zmodAdd p prime.left (NatPrime_empty_absurd prime) x y) :=
    frobenius_id prime
      (zmodAdd p prime.left (NatPrime_empty_absurd prime) x y)
  have rightId :
      zmodEq
        (zmodAdd p prime.left (NatPrime_empty_absurd prime)
          (frobenius prime x) (frobenius prime y))
        (zmodAdd p prime.left (NatPrime_empty_absurd prime) x y) :=
    zmodAdd_congr prime.left (NatPrime_empty_absurd prime)
      (frobenius_id prime x) (frobenius_id prime y)
  exact zmodEq_trans leftId (zmodEq_symm rightId)

theorem frobenius_mul {p : BHist} (prime : NatPrime p)
    (x y : ZMod p) :
    zmodEq
      (frobenius prime
        (zmodMul p prime.left (NatPrime_empty_absurd prime) x y))
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (frobenius prime x) (frobenius prime y)) := by
  have leftId :
      zmodEq
        (frobenius prime
          (zmodMul p prime.left (NatPrime_empty_absurd prime) x y))
        (zmodMul p prime.left (NatPrime_empty_absurd prime) x y) :=
    frobenius_id prime
      (zmodMul p prime.left (NatPrime_empty_absurd prime) x y)
  have rightId :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (frobenius prime x) (frobenius prime y))
        (zmodMul p prime.left (NatPrime_empty_absurd prime) x y) :=
    zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      (frobenius_id prime x) (frobenius_id prime y)
  exact zmodEq_trans leftId (zmodEq_symm rightId)

def frobeniusRingAut {p : BHist} (prime : NatPrime p) :
    RelRingEquiv (ZMod p) zmodEq (ZMod p) zmodEq where
  source := (zmodRelCommRing prime).toRelRing
  target := (zmodRelCommRing prime).toRelRing
  toFun := frobenius prime
  invFun := fun x => x
  map_rel := by
    intro x y
    exact frobenius_respects prime
  inv_rel := by
    intro _x _y same
    exact same
  left_inv_rel := by
    intro x
    exact frobenius_id prime x
  right_inv_rel := by
    intro y
    exact frobenius_id prime y
  map_zero := frobenius_zero prime
  map_one := frobenius_one prime
  map_add := frobenius_freshmanDream prime
  map_mul := frobenius_mul prime

end BEDC.Derived.FrobeniusUp
