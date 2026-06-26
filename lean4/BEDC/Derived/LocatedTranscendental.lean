import BEDC.Derived.RationalUp.FieldLaws
import BEDC.Derived.FactorialUp

namespace BEDC.Derived.LocatedTranscendental

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.RationalUp

abbrev ratNatOne : BHist :=
  BEDC.Derived.PadicUp.NatOne

def natHist (n : Nat) : BHist :=
  natToUnary n

theorem natHist_unary (n : Nat) : UnaryHistory (natHist n) :=
  natToUnary_unary n

theorem natHist_length (n : Nat) : bwordLength (natHist n) = n :=
  natToUnary_length n

theorem natHist_succ_pos (n : Nat) :
    NatUnaryStrictPrefix ratNatOne (natHist (n + 2)) ∨
      hsame (natHist (n + 2)) ratNatOne := by
  apply Or.inl
  apply BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
  · change UnaryHistory (BHist.e1 BHist.Empty)
    exact unary_e1_closed unary_empty
  · exact natHist_unary (n + 2)
  · change bwordLength (BHist.e1 BHist.Empty) < bwordLength (natHist (n + 2))
    rw [natHist_length]
    exact Nat.succ_lt_succ (Nat.zero_lt_succ n)

def natRat (n : Nat) : RatNum :=
  intToRat (intOfNat (natHist n) (natHist_unary n))

def natPosRat (n : Nat) : RatNum :=
  natRat (n + 1)

def unitFraction (n : Nat) : RatNum :=
  { num := intOne
    den := natHist (n + 1)
    den_pos := by
      cases n with
      | zero =>
          exact Or.inr (hsame_refl ratNatOne)
      | succ n =>
          exact natHist_succ_pos n }

def intPow (x : RatNum) : Nat -> RatNum
  | 0 => ratOne
  | n + 1 => ratMul x (intPow x n)

def factorialNat : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialNat n

theorem factorialNat_pos (n : Nat) : 0 < factorialNat n := by
  induction n with
  | zero =>
      exact Nat.succ_pos 0
  | succ n ih =>
      exact Nat.mul_pos (Nat.succ_pos n) ih

theorem factorialNat_succ_pos (n : Nat) :
    0 < factorialNat (n + 1) := by
  exact factorialNat_pos (n + 1)

theorem factorialNat_as_succ (n : Nat) :
    ∃ k : Nat, factorialNat n = k + 1 := by
  exact Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (factorialNat_pos n))

def factorialRat (n : Nat) : RatNum :=
  natRat (factorialNat n)

theorem factorialNat_den_pos (n : Nat) :
    NatUnaryStrictPrefix ratNatOne (natHist (factorialNat (n + 1))) ∨
      hsame (natHist (factorialNat (n + 1))) ratNatOne := by
  have asSucc := factorialNat_as_succ (n + 1)
  cases asSucc with
  | intro k hk =>
      cases k with
      | zero =>
          rw [hk]
          exact Or.inr (hsame_refl ratNatOne)
      | succ k =>
          rw [hk]
          exact natHist_succ_pos k

def invFactorialRat (n : Nat) : RatNum :=
  { num := intOne
    den := natHist (factorialNat n)
    den_pos := by
      cases n with
      | zero =>
          exact Or.inr (hsame_refl ratNatOne)
      | succ n =>
          exact factorialNat_den_pos n }

def expTerm (x : RatNum) (k : Nat) : RatNum :=
  ratMul (intPow x k) (invFactorialRat k)

def sumRatList : List RatNum -> RatNum
  | [] => ratZero
  | x :: xs => ratAdd x (sumRatList xs)

def expTermList (x : RatNum) : Nat -> List RatNum
  | 0 => [ratOne]
  | n + 1 => expTermList x n ++ [expTerm x (n + 1)]

def ratExp (x : RatNum) (n : Nat) : RatNum :=
  sumRatList (expTermList x n)

def expTailBudget (xBound : Nat) (n : Nat) : RatNum :=
  unitFraction (n + xBound + 1)

def ratExpTailBudget (_x : RatNum) (xBound n : Nat) : RatNum :=
  expTailBudget xBound n

def lnTermPositive : Nat -> Bool
  | 0 => true
  | k + 1 =>
      match lnTermPositive k with
      | true => false
      | false => true

def lnOnePlusTerm (u : RatNum) (k : Nat) : RatNum :=
  let term := ratMul (intPow u (k + 1)) (unitFraction k)
  match lnTermPositive k with
  | true => term
  | false => ratNeg term

def lnOnePlusTermList (u : RatNum) : Nat -> List RatNum
  | 0 => [u]
  | n + 1 => lnOnePlusTermList u n ++ [lnOnePlusTerm u (n + 1)]

def ratLnOnePlus (u : RatNum) (n : Nat) : RatNum :=
  sumRatList (lnOnePlusTermList u n)

def ratLnAroundOne (x : RatNum) (n : Nat) : RatNum :=
  ratLnOnePlus (ratAdd x (ratNeg ratOne)) n

def lnTailBudget (u : RatNum) (n : Nat) : RatNum :=
  ratMul (unitFraction (2 * (n + 1) + 1)) (ratAdd u ratOne)

structure RatWindow where
  lo : RatNum
  hi : RatNum
  widthBound : RatNum

def expWindow (x : RatNum) (xBound n : Nat) : RatWindow :=
  { lo := ratExp x n
    hi := ratAdd (ratExp x n) (ratExpTailBudget x xBound n)
    widthBound := ratExpTailBudget x xBound n }

def lnOnePlusWindow (u : RatNum) (n : Nat) : RatWindow :=
  { lo := ratLnOnePlus u n
    hi := ratAdd (ratLnOnePlus u n) (lnTailBudget u n)
    widthBound := lnTailBudget u n }

structure RatApproximationSchedule where
  window : Nat -> RatWindow
  fuel : Nat

def expRationalApproximation (x : RatNum) (xBound : Nat) :
    RatApproximationSchedule :=
  { window := expWindow x xBound
    fuel := xBound }

def lnOnePlusRationalApproximation (u : RatNum) :
    RatApproximationSchedule :=
  { window := lnOnePlusWindow u
    fuel := 0 }

theorem ratExp_zero :
    RatEq (ratExp ratZero 0) ratOne := by
  unfold ratExp expTermList sumRatList
  exact RatEq_trans (ratAdd ratOne ratZero) ratOne ratOne
    (ratAdd_zero_right ratOne) (RatEq_refl ratOne)

theorem ratLnOnePlus_zero :
    RatEq (ratLnOnePlus ratZero 0) ratZero := by
  unfold ratLnOnePlus lnOnePlusTermList sumRatList
  exact ratZero_add_left ratZero

theorem expRationalApproximation_window_zero (x : RatNum) (xBound : Nat) :
    (expRationalApproximation x xBound).window 0 = expWindow x xBound 0 := by
  rfl

theorem lnOnePlusRationalApproximation_window_zero (u : RatNum) :
    (lnOnePlusRationalApproximation u).window 0 = lnOnePlusWindow u 0 := by
  rfl

theorem exp_window_readback (x : RatNum) (xBound n : Nat) :
    (expRationalApproximation x xBound).window n = expWindow x xBound n := by
  rfl

theorem ln_one_plus_window_readback (u : RatNum) (n : Nat) :
    (lnOnePlusRationalApproximation u).window n = lnOnePlusWindow u n := by
  rfl

theorem exp_ln_schedule_fuel_readback (x u : RatNum) :
    (lnOnePlusRationalApproximation u).fuel = 0 ∧
      (expRationalApproximation x 0).fuel = 0 := by
  exact ⟨rfl, rfl⟩

def sampleExpLower : RatNum := natRat 2

def sampleExpUpper : RatNum :=
  ratAdd (natRat 2) (unitFraction 1)

def sampleLnLower : RatNum :=
  unitFraction 2

def sampleLnUpper : RatNum :=
  ratAdd (unitFraction 2) (unitFraction 4)

def sampleExpWindow : RatWindow :=
  { lo := sampleExpLower
    hi := sampleExpUpper
    widthBound := unitFraction 1 }

def sampleLnWindow : RatWindow :=
  { lo := sampleLnLower
    hi := sampleLnUpper
    widthBound := unitFraction 4 }

theorem sample_exp_window_width :
    sampleExpWindow.widthBound = unitFraction 1 := by
  rfl

theorem sample_ln_window_width :
    sampleLnWindow.widthBound = unitFraction 4 := by
  rfl

end BEDC.Derived.LocatedTranscendental
