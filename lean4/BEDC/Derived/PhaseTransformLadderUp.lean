import BEDC.Algebra.Rel.Basic
import BEDC.Derived.LocatedTranscendental

namespace BEDC.Derived.PhaseTransformLadderUp

open BEDC.Algebra.Rel
open BEDC.Derived.LocatedReal
open BEDC.Derived.LocatedTranscendental
open BEDC.Derived.RationalUp

variable {A : Type u} {r : A -> A -> Prop}

abbrev AddAxis (_R : RelCommRing A r) :=
  A

abbrev MulAxis (_R : RelCommRing A r) :=
  A

structure RelMulOne (A : Type u) (r : A -> A -> Prop) where
  one : A
  mul : A -> A -> A
  refl : ∀ x : A, r x x
  symm : ∀ {x y : A}, r x y -> r y x
  trans : ∀ {x y z : A}, r x y -> r y z -> r x z
  mul_congr :
    ∀ {x x' y y' : A}, r x x' -> r y y' -> r (mul x y) (mul x' y')
  mul_assoc : ∀ x y z : A, r (mul (mul x y) z) (mul x (mul y z))
  mul_one : ∀ x : A, r (mul x one) x
  one_mul : ∀ x : A, r (mul one x) x
  mul_comm : ∀ x y : A, r (mul x y) (mul y x)

def RelMulOne.ofRelCommRing (R : RelCommRing A r) : RelMulOne A r where
  one := R.one
  mul := R.mul
  refl := R.refl
  symm := by
    intro x y
    exact R.symm
  trans := by
    intro x y z
    exact R.trans
  mul_congr := R.mul_congr
  mul_assoc := R.mul_assoc
  mul_one := R.mul_one
  one_mul := R.one_mul
  mul_comm := R.mul_comm

def ladderPow (M : RelMulOne A r) (a : A) : Nat -> A
  | 0 => M.one
  | n + 1 => M.mul (ladderPow M a n) a

def ladderPowList (a : A) : Nat -> List A
  | 0 => []
  | n + 1 => ladderPowList a n ++ [a]

def ladderProd (M : RelMulOne A r) : List A -> A
  | [] => M.one
  | x :: xs => M.mul x (ladderProd M xs)

structure LocatedExpLogBridge (K : RatMetricKit) where
  exp : LReal K -> LReal K
  log : LReal K -> LReal K
  mul : LReal K -> LReal K -> LReal K
  exp_respects :
    ∀ {x y : LReal K}, LRealEq K x y -> LRealEq K (exp x) (exp y)
  log_respects :
    ∀ {x y : LReal K}, LRealEq K x y -> LRealEq K (log x) (log y)
  mul_respects :
    ∀ {x x' y y' : LReal K},
      LRealEq K x x' -> LRealEq K y y' ->
        LRealEq K (mul x y) (mul x' y')
  exp_add_mul :
    ∀ x y : LReal K, LRealEq K (exp (lrAdd x y)) (mul (exp x) (exp y))
  log_mul_add :
    ∀ x y : LReal K, LRealEq K (log (mul x y)) (lrAdd (log x) (log y))

theorem exp_add_to_mul_bridge {K : RatMetricKit}
    (bridge : LocatedExpLogBridge K) (x y : LReal K) :
    LRealEq K (bridge.exp (lrAdd x y))
      (bridge.mul (bridge.exp x) (bridge.exp y)) :=
  bridge.exp_add_mul x y

theorem log_mul_to_add_bridge {K : RatMetricKit}
    (bridge : LocatedExpLogBridge K) (x y : LReal K) :
    LRealEq K (bridge.log (bridge.mul x y))
      (lrAdd (bridge.log x) (bridge.log y)) :=
  bridge.log_mul_add x y

theorem exp_bridge_respects_add_input {K : RatMetricKit}
    (bridge : LocatedExpLogBridge K) {x x' y y' : LReal K} :
    LRealEq K x x' ->
      LRealEq K y y' ->
        LRealEq K (bridge.exp (lrAdd x y))
          (bridge.exp (lrAdd x' y')) := by
  intro hx hy
  exact bridge.exp_respects (lrAdd_respects hx hy)

theorem ladderPow_zero (M : RelMulOne A r) (a : A) :
    r (ladderPow M a 0) M.one :=
  M.refl M.one

theorem ladderPow_succ (M : RelMulOne A r) (a : A) (n : Nat) :
    r (ladderPow M a (n + 1)) (M.mul (ladderPow M a n) a) :=
  M.refl (ladderPow M a (n + 1))

private theorem ladderProd_snoc (M : RelMulOne A r) :
    ∀ xs : List A, ∀ x : A,
      r (ladderProd M (xs ++ [x])) (M.mul (ladderProd M xs) x)
  | [], x =>
      M.trans (M.mul_one x) (M.symm (M.one_mul x))
  | y :: ys, x => by
      have tail := ladderProd_snoc M ys x
      have step :
          r (M.mul y (ladderProd M (ys ++ [x])))
            (M.mul y (M.mul (ladderProd M ys) x)) :=
        M.mul_congr (M.refl y) tail
      exact M.trans step (M.symm (M.mul_assoc y (ladderProd M ys) x))

theorem ladderPow_listProd (M : RelMulOne A r) (a : A) :
    ∀ n : Nat, r (ladderPow M a n) (ladderProd M (ladderPowList a n))
  | 0 =>
      M.refl M.one
  | n + 1 => by
      have tail := ladderPow_listProd M a n
      have step :
          r (M.mul (ladderPow M a n) a)
            (M.mul (ladderProd M (ladderPowList a n)) a) :=
        M.mul_congr tail (M.refl a)
      have snoc :
          r (ladderProd M (ladderPowList a n ++ [a]))
            (M.mul (ladderProd M (ladderPowList a n)) a) :=
        ladderProd_snoc M (ladderPowList a n) a
      exact M.trans step (M.symm snoc)

private theorem relPow_add_aux (M : RelMulOne A r) (a : A) :
    ∀ m n : Nat,
      r (ladderPow M a (m + n))
        (M.mul (ladderPow M a m) (ladderPow M a n))
  | m, 0 => by
      rw [Nat.add_zero]
      exact M.symm (M.mul_one (ladderPow M a m))
  | m, n + 1 => by
      change r (M.mul (ladderPow M a (m + n)) a)
        (M.mul (ladderPow M a m) (M.mul (ladderPow M a n) a))
      have tail := relPow_add_aux M a m n
      have assocForward :
          r (M.mul (M.mul (ladderPow M a m) (ladderPow M a n)) a)
            (M.mul (ladderPow M a m) (M.mul (ladderPow M a n) a)) :=
        M.mul_assoc (ladderPow M a m) (ladderPow M a n) a
      exact M.trans (M.mul_congr tail (M.refl a))
        assocForward

theorem relPow_add_ladder (M : RelMulOne A r) (a : A) (m n : Nat) :
    r (ladderPow M a (m + n))
      (M.mul (ladderPow M a m) (ladderPow M a n)) :=
  relPow_add_aux M a m n

theorem relPow_one_ladder (M : RelMulOne A r) (a : A) :
    r (ladderPow M a 1) a :=
  M.one_mul a

theorem relPow_two_ladder (M : RelMulOne A r) (a : A) :
    r (ladderPow M a 2) (M.mul a a) :=
  M.mul_congr (relPow_one_ladder M a) (M.refl a)

def relCommRingMulOne (R : RelCommRing A r) : RelMulOne A r :=
  RelMulOne.ofRelCommRing R

theorem relCommRingPow_add_ladder (R : RelCommRing A r) (a : A) (m n : Nat) :
    r (ladderPow (relCommRingMulOne R) a (m + n))
      (R.mul (ladderPow (relCommRingMulOne R) a m)
        (ladderPow (relCommRingMulOne R) a n)) :=
  relPow_add_ladder (relCommRingMulOne R) a m n

def rationalMulOne : RelMulOne RatNum RatEq where
  one := ratOne
  mul := ratMul
  refl := RatEq_refl
  symm := by
    intro x y
    exact RatEq_symm
  trans := by
    intro x y z
    exact RatEq_trans x y z
  mul_congr := by
    intro x x' y y'
    exact ratMul_respects
  mul_assoc := ratMul_assoc
  mul_one := ratMul_one_right
  one_mul := ratOne_mul_left
  mul_comm := ratMul_comm

def rationalLadderPow (a : RatNum) (n : Nat) : RatNum :=
  ladderPow rationalMulOne a n

def rationalRootWitness (base root : RatNum) (height : Nat) : Prop :=
  RatEq (rationalLadderPow root height) base

def rationalLogScaleWitness (bridgeFrom bridgeTo : RatNum) (height : Nat)
    (logBridge : RatNum) : Prop :=
  RatEq bridgeTo (ratAdd bridgeFrom logBridge) ∧
    rationalRootWitness bridgeTo logBridge height

theorem rational_ladderPow_zero (a : RatNum) :
    RatEq (rationalLadderPow a 0) ratOne :=
  rationalMulOne.refl ratOne

theorem rational_ladderPow_succ (a : RatNum) (n : Nat) :
    RatEq (rationalLadderPow a (n + 1))
      (ratMul (rationalLadderPow a n) a) :=
  rationalMulOne.refl (rationalLadderPow a (n + 1))

theorem rational_ladderPow_add (a : RatNum) (m n : Nat) :
    RatEq (rationalLadderPow a (m + n))
      (ratMul (rationalLadderPow a m) (rationalLadderPow a n)) :=
  relPow_add_ladder rationalMulOne a m n

theorem rational_ladderPow_listProd (a : RatNum) (n : Nat) :
    RatEq (rationalLadderPow a n)
      (ladderProd rationalMulOne (ladderPowList a n)) :=
  ladderPow_listProd rationalMulOne a n

theorem rational_root_witness_readback {base root : RatNum} {height : Nat} :
    rationalRootWitness base root height ->
      RatEq (rationalLadderPow root height) base :=
  fun h => h

theorem rational_log_scale_readback {bridgeFrom bridgeTo : RatNum}
    {height : Nat} {logBridge : RatNum} :
    rationalLogScaleWitness bridgeFrom bridgeTo height logBridge ->
      RatEq bridgeTo (ratAdd bridgeFrom logBridge) ∧
        rationalRootWitness bridgeTo logBridge height :=
  fun h => h

#check exp_add_to_mul_bridge
#check relPow_add_ladder
#check rational_ladderPow_add
#check rational_root_witness_readback

end BEDC.Derived.PhaseTransformLadderUp
