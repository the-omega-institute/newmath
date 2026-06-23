import BEDC.Derived.PadicUp.Localization

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

def zpOfNat (p : BHist) (prime : NatPrime p) (n : BHist)
    (nUnary : UnaryHistory n) : ZpInt p :=
  natToZp p prime n nUnary

def zpPow (p : BHist) (x : ZpInt p) : Nat -> ZpInt p
  | 0 => zpOne p x.prime
  | n + 1 => zpMul p (zpPow p x n) x

def zpGeom (p : BHist) (x : ZpInt p) : Nat -> ZpInt p
  | 0 => zpZero p x.prime
  | n + 1 => zpAdd p (zpGeom p x n) (zpPow p x n)

def ZpUnit {p : BHist} (a : ZpInt p) : Prop :=
  (zpLevel a (BHist.e1 BHist.Empty) (unary_e1_closed unary_empty)).val ≠ BHist.Empty

private def unitResidue {p : BHist} (a : ZpInt p) : BoundedNat p :=
  { val := (zpLevel a (BHist.e1 BHist.Empty) (unary_e1_closed unary_empty)).val
    isLt := by
      have oneSame : hsame (pPowCanon p (BHist.e1 BHist.Empty)) p := by
        change hsame (zpuNatToUnary (bwordLength p ^ 1)) p
        exact zpu_hsame_of_unary_length (zpuNatToUnary_unary _) a.prime.left
          ((zpuNatToUnary_length _).trans (Nat.one_mul (bwordLength p)))
      exact NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure
        (zpLevel a (BHist.e1 BHist.Empty) (unary_e1_closed unary_empty)).isLt
        oneSame }

private theorem unitResidue_nonzero {p : BHist} (a : ZpInt p) :
    ZpUnit a -> hsame (unitResidue a).val BHist.Empty -> False := by
  intro unit sameZero
  exact unit sameZero

def ZpUnitSeedInv {p : BHist} (a : ZpInt p) (unit : ZpUnit a) : ZpInt p :=
  zpOfNat p a.prime (invModPrime a.prime (unitResidue a)
    (unitResidue_nonzero a unit)).val
    (BoundedNat_unary a.prime.left
      (invModPrime a.prime (unitResidue a) (unitResidue_nonzero a unit)))

theorem ZpUnitSeedInv_mod_p {p : BHist} (a : ZpInt p) (unit : ZpUnit a) :
    hsame
      (natModFn p
        (natMulFn
          (zpLevel a (BHist.e1 BHist.Empty) (unary_e1_closed unary_empty)).val
          (zpLevel (ZpUnitSeedInv a unit) (BHist.e1 BHist.Empty)
            (unary_e1_closed unary_empty)).val))
      (natModFn p NatOne) := by
  unfold ZpUnitSeedInv zpOfNat zpLevel
  change hsame
    (natModFn p
      (natMulFn
        (unitResidue a).val
        (natModFn (pPowCanon p (BHist.e1 BHist.Empty))
          (invModPrime a.prime (unitResidue a)
            (unitResidue_nonzero a unit)).val)))
    (natModFn p NatOne)
  have onePowerSame : hsame (pPowCanon p (BHist.e1 BHist.Empty)) p := by
    change hsame (zpuNatToUnary (bwordLength p ^ 1)) p
    exact zpu_hsame_of_unary_length (zpuNatToUnary_unary _) a.prime.left
      ((zpuNatToUnary_length _).trans (Nat.one_mul (bwordLength p)))
  have invUnary : UnaryHistory
      (invModPrime a.prime (unitResidue a)
        (unitResidue_nonzero a unit)).val :=
    BoundedNat_unary a.prime.left
      (invModPrime a.prime (unitResidue a)
        (unitResidue_nonzero a unit))
  have reduceInv :
      hsame
        (natModFn (pPowCanon p (BHist.e1 BHist.Empty))
          (invModPrime a.prime (unitResidue a)
            (unitResidue_nonzero a unit)).val)
        (invModPrime a.prime (unitResidue a)
          (unitResidue_nonzero a unit)).val := by
    exact natModFn_of_strict
      (pPowCanon_unary p (BHist.e1 BHist.Empty))
      (pPowCanon_nonempty_of_prime a.prime (unary_e1_closed unary_empty))
      invUnary
      (NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure
        (invModPrime a.prime (unitResidue a)
          (unitResidue_nonzero a unit)).isLt
        (hsame_symm onePowerSame))
  have productTransport :
      hsame
        (natModFn p
          (natMulFn
            (unitResidue a).val
            (natModFn (pPowCanon p (BHist.e1 BHist.Empty))
              (invModPrime a.prime (unitResidue a)
                (unitResidue_nonzero a unit)).val)))
        (natModFn p
          (natMulFn
            (unitResidue a).val
            (invModPrime a.prime (unitResidue a)
              (unitResidue_nonzero a unit)).val)) :=
    natModFn_hsame_arg_transport (M := p)
      (natMulFn_hsame_transport (hsame_refl _) reduceInv)
  exact hsame_trans productTransport
    (invModPrime_spec a.prime (unitResidue a)
      (unitResidue_nonzero a unit))

def ZpUnitError {p : BHist} (a : ZpInt p) (unit : ZpUnit a) : ZpInt p :=
  zpSub p (zpOne p a.prime) (zpMul p a (ZpUnitSeedInv a unit))

structure ZpApart0 {p : BHist} (a : ZpInt p) where
  N : Nat
  pos : 0 < N
  nz : (zpLevel a (zpuNatToUnary N) (zpuNatToUnary_unary N)).val ≠ BHist.Empty

structure ZpValWitness {p : BHist} (a : ZpInt p) where
  k : Nat
  zero_k : (zpLevel a (zpuNatToUnary k) (zpuNatToUnary_unary k)).val = BHist.Empty
  nz_succ :
    (zpLevel a (zpuNatToUnary (k + 1)) (zpuNatToUnary_unary (k + 1))).val ≠ BHist.Empty

theorem zpLevel_zero_val_empty {p : BHist} (a : ZpInt p) :
    (zpLevel a (zpuNatToUnary 0) (zpuNatToUnary_unary 0)).val = BHist.Empty := by
  have powerZeroSame : hsame (pPowCanon p (zpuNatToUnary 0)) NatOne := by
    change hsame (pPowCanon p BHist.Empty) NatOne
    exact hsame_symm
      (PPow_functional (PPow.zero a.prime.left)
        (pPowCanon_PPow a.prime.left unary_empty))
  have xStrict :
      NatUnaryStrictPrefix
        (zpLevel a (zpuNatToUnary 0) (zpuNatToUnary_unary 0)).val
        NatOne :=
    NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure
      (zpLevel a (zpuNatToUnary 0) (zpuNatToUnary_unary 0)).isLt
      powerZeroSame
  have xUnary :
      UnaryHistory (zpLevel a (zpuNatToUnary 0) (zpuNatToUnary_unary 0)).val :=
    BoundedNat_unary (pPowCanon_unary p (zpuNatToUnary 0))
      (zpLevel a (zpuNatToUnary 0) (zpuNatToUnary_unary 0))
  have boundary :=
    NatUnaryStrictPrefix_successor_boundary_local xUnary xStrict
  cases boundary with
  | inl sameZero =>
      exact sameZero
  | inr strictEmpty =>
      exact False.elim (NatUnaryStrictPrefix_empty_right_absurd strictEmpty)

private def firstNonzeroFromTop {p : BHist} (a : ZpInt p) :
    (n : Nat) ->
      (zpLevel a (zpuNatToUnary n) (zpuNatToUnary_unary n)).val ≠ BHist.Empty ->
        ZpValWitness a
  | 0, nz =>
      False.elim (nz (zpLevel_zero_val_empty a))
  | n + 1, nz =>
      if zero :
          (zpLevel a (zpuNatToUnary n) (zpuNatToUnary_unary n)).val = BHist.Empty then
        { k := n
          zero_k := zero
          nz_succ := nz }
      else
        firstNonzeroFromTop a n zero

def firstNonzero {p : BHist} {a : ZpInt p} (apart : ZpApart0 a) : ZpValWitness a :=
  firstNonzeroFromTop a apart.N apart.nz

structure QpApart0 {p : BHist} (x : QpInt p) where
  num_apart : ZpApart0 x.value

structure QpApartLocalizationCore (p : BHist) where
  carrier : Type
  eqv : carrier -> carrier -> Prop
  zero : NatPrime p -> carrier
  one : NatPrime p -> carrier
  mul : carrier -> carrier -> carrier
  apart_zero : carrier -> Type

def QpInt_apart_localization_core (p : BHist) : QpApartLocalizationCore p :=
  { carrier := QpInt p
    eqv := QpEq
    zero := qpZero p
    one := qpOne p
    mul := qpMul
    apart_zero := QpApart0 }

end BEDC.Derived.PadicUp
