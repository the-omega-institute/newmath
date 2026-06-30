import BEDC.Derived.HarmonicUp
import BEDC.Derived.BinomialIdentitiesUp

namespace BEDC.Derived.HyperharmonicUp

open BEDC.Derived.RationalUp
open BEDC.Derived.HarmonicUp

def hyperharmonicBase : Nat -> RatNum
  | 0 => ratZero
  | Nat.succ n => oneOverNatSucc n

def ratPrefixSumFromOne (f : Nat -> RatNum) : Nat -> RatNum
  | 0 => ratZero
  | Nat.succ n => ratAdd (ratPrefixSumFromOne f n) (f (Nat.succ n))

def hyperharmonic : Nat -> Nat -> RatNum
  | n, 0 => hyperharmonicBase n
  | n, Nat.succ r => ratPrefixSumFromOne (fun k => hyperharmonic k r) n

def natRat : Nat -> RatNum
  | 0 => ratZero
  | Nat.succ 0 => ratOne
  | Nat.succ (Nat.succ n) =>
      BEDC.Derived.BernoulliUp.ratOfIntOverNat
        (Int.ofNat (Nat.succ (Nat.succ n))) 0

def hyperharmonicClosed (n r : Nat) : RatNum :=
  match r with
  | 0 => hyperharmonicBase n
  | Nat.succ r0 =>
      ratMul (natRat (BEDC.Derived.BinomialIdentitiesUp.C (n + r0) r0))
        (ratSub (harmonic (n + r0)) (harmonic r0))

theorem hyperharmonic_zero_order_zero :
    RatEq (hyperharmonic 0 0) ratZero := by
  exact RatEq_refl ratZero

theorem hyperharmonic_zero_order_succ (n : Nat) :
    RatEq (hyperharmonic (Nat.succ n) 0) (oneOverNatSucc n) := by
  exact RatEq_refl (oneOverNatSucc n)

theorem ratPrefixSumFromOne_zero (f : Nat -> RatNum) :
    RatEq (ratPrefixSumFromOne f 0) ratZero := by
  exact RatEq_refl ratZero

theorem ratPrefixSumFromOne_succ (f : Nat -> RatNum) (n : Nat) :
    RatEq (ratPrefixSumFromOne f (Nat.succ n))
      (ratAdd (ratPrefixSumFromOne f n) (f (Nat.succ n))) := by
  exact RatEq_refl _

theorem hyperharmonic_succ (n r : Nat) :
    RatEq (hyperharmonic n (Nat.succ r))
      (ratPrefixSumFromOne (fun k => hyperharmonic k r) n) := by
  exact RatEq_refl _

theorem hyperharmonic_one_eq_harmonic (n : Nat) :
    hyperharmonic n 1 = harmonic n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change ratAdd (hyperharmonic n 1) (oneOverNatSucc n) =
        ratAdd (harmonic n) (oneOverNatSucc n)
      exact congrArg (fun h => ratAdd h (oneOverNatSucc n)) ih

theorem hyperharmonic_one_ratEq_harmonic (n : Nat) :
    RatEq (hyperharmonic n 1) (harmonic n) := by
  rw [hyperharmonic_one_eq_harmonic n]
  exact RatEq_refl (harmonic n)

theorem natRat_choose_zero (n : Nat) :
    RatEq (natRat (BEDC.Derived.BinomialIdentitiesUp.C n 0)) ratOne := by
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n]
  exact RatEq_refl ratOne

theorem ratNeg_zero :
    RatEq (ratNeg ratZero) ratZero := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratZero intToRat
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_zero
  · unfold ratDenInt ratNeg ratZero intToRat
    exact IntEq_refl _

theorem ratSub_zero_right (x : RatNum) :
    RatEq (ratSub x ratZero) x := by
  unfold ratSub
  exact RatEq_trans (ratAdd x (ratNeg ratZero)) (ratAdd x ratZero) x
    (ratAdd_respects (RatEq_refl x) ratNeg_zero)
    (ratAdd_zero_right x)

theorem ratSub_right_respects {x y y' : RatNum} :
    RatEq y y' -> RatEq (ratSub x y) (ratSub x y') := by
  intro same
  unfold ratSub
  exact ratAdd_respects (RatEq_refl x) (ratNeg_respects same)

theorem harmonic_gap_zero_right (n : Nat) :
    RatEq (ratSub (harmonic n) (harmonic 0)) (harmonic n) := by
  exact RatEq_trans
    (ratSub (harmonic n) (harmonic 0))
    (ratSub (harmonic n) ratZero)
    (harmonic n)
    (ratSub_right_respects (x := harmonic n) harmonic_zero)
    (ratSub_zero_right (harmonic n))

theorem hyperharmonic_binomial_harmonic_first_order (n : Nat) :
    RatEq (hyperharmonic n 1)
      (ratMul (natRat (BEDC.Derived.BinomialIdentitiesUp.C (n + 0) 0))
        (ratSub (harmonic (n + 0)) (harmonic 0))) := by
  rw [Nat.add_zero]
  have scaleGap :
      RatEq
        (ratMul (natRat (BEDC.Derived.BinomialIdentitiesUp.C n 0))
          (ratSub (harmonic n) (harmonic 0)))
        (ratMul ratOne (harmonic n)) :=
    ratMul_respects (natRat_choose_zero n) (harmonic_gap_zero_right n)
  have closedToHarmonic :
      RatEq
        (ratMul (natRat (BEDC.Derived.BinomialIdentitiesUp.C n 0))
          (ratSub (harmonic n) (harmonic 0)))
        (harmonic n) :=
    RatEq_trans
      (ratMul (natRat (BEDC.Derived.BinomialIdentitiesUp.C n 0))
        (ratSub (harmonic n) (harmonic 0)))
      (ratMul ratOne (harmonic n))
      (harmonic n)
      scaleGap
      (ratOne_mul_left (harmonic n))
  exact RatEq_trans
    (hyperharmonic n 1)
    (harmonic n)
    (ratMul (natRat (BEDC.Derived.BinomialIdentitiesUp.C n 0))
      (ratSub (harmonic n) (harmonic 0)))
    (hyperharmonic_one_ratEq_harmonic n)
    (RatEq_symm closedToHarmonic)

theorem hyperharmonic_closed_first_order (n : Nat) :
    RatEq (hyperharmonic n 1) (hyperharmonicClosed n 1) := by
  change RatEq (hyperharmonic n 1)
    (ratMul (natRat (BEDC.Derived.BinomialIdentitiesUp.C (n + 0) 0))
      (ratSub (harmonic (n + 0)) (harmonic 0)))
  exact hyperharmonic_binomial_harmonic_first_order n

end BEDC.Derived.HyperharmonicUp
