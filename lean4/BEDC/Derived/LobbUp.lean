import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.CatalanUp
import BEDC.Derived.IntUp
import BEDC.Derived.RationalUp

namespace BEDC.Derived.LobbUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def intOfNatStd (n : Nat) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat (natToUnary n) (natToUnary_unary n)

abbrev zzero : IntegerUp :=
  integerRing.zero

abbrev zadd : IntegerUp -> IntegerUp -> IntegerUp :=
  integerRing.add

abbrev zneg : IntegerUp -> IntegerUp :=
  integerRing.neg

abbrev zsub : IntegerUp -> IntegerUp -> IntegerUp :=
  integerRing.sub

def lobbTop (n : Nat) : Nat :=
  n + n

def lobbLowerIndex (m n : Nat) : Nat :=
  n + m

def lobbUpperIndex (m n : Nat) : Nat :=
  Nat.succ (n + m)

def lobbDenominator (m n : Nat) : Nat :=
  m + n + 1

def lobbScaledBinomialNumerator (m n : Nat) : Nat :=
  (2 * m + 1) * C (lobbTop n) (lobbLowerIndex m n)

def lobbNat (m n : Nat) : Nat :=
  C (lobbTop n) (lobbLowerIndex m n) -
    C (lobbTop n) (lobbUpperIndex m n)

def catalanNat (n : Nat) : Nat :=
  C (lobbTop n) n - C (lobbTop n) (Nat.succ n)

def lobbInteger (m n : Nat) : IntegerUp :=
  zsub
    (intOfNatStd (C (lobbTop n) (lobbLowerIndex m n)))
    (intOfNatStd (C (lobbTop n) (lobbUpperIndex m n)))

def catalanInteger (n : Nat) : IntegerUp :=
  zsub
    (intOfNatStd (C (lobbTop n) n))
    (intOfNatStd (C (lobbTop n) (Nat.succ n)))

def lobbRowSumNat (n : Nat) : Nat :=
  finiteNatSum (fun m => lobbNat m n) n

def intFiniteSum (f : Nat -> IntegerUp) : Nat -> IntegerUp
  | 0 => f 0
  | Nat.succ n => zadd (intFiniteSum f n) (f (Nat.succ n))

def lobbRowSumInteger (n : Nat) : IntegerUp :=
  intFiniteSum (fun m => lobbInteger m n) n

def lobbCentralBinomialInteger (n : Nat) : IntegerUp :=
  intOfNatStd (C (lobbTop n) n)

private theorem zsub_congr {a a' b b' : IntegerUp} :
    IntEq a a' -> IntEq b b' -> IntEq (zsub a b) (zsub a' b') := by
  intro ha hb
  unfold zsub
  exact integerRing.add_congr ha (integerRing.neg_congr hb)

private theorem zsub_zero_right (a : IntegerUp) :
    IntEq (zsub a zzero) a := by
  unfold zsub zzero
  exact integerRing.trans
    (integerRing.sub_eq_add_neg a integerRing.zero)
    (integerRing.trans
      (integerRing.add_congr (integerRing.refl a) integerRing.neg_zero)
      (integerRing.add_zero a))

private theorem zsub_add_zsub_cancel_middle (a b c : IntegerUp) :
    IntEq (zadd (zsub a b) (zsub b c)) (zsub a c) := by
  unfold zadd zsub
  exact integerRing.trans
    (integerRing.add_congr
      (integerRing.sub_eq_add_neg a b)
      (integerRing.sub_eq_add_neg b c))
    (integerRing.trans
      (integerRing.add_assoc a (zneg b) (integerRing.add b (zneg c)))
      (integerRing.trans
        (integerRing.add_congr (integerRing.refl a)
          (integerRing.trans
            (integerRing.symm
              (integerRing.add_assoc (zneg b) b (zneg c)))
            (integerRing.trans
              (integerRing.add_congr (integerRing.neg_add b)
                (integerRing.refl (zneg c)))
              (integerRing.zero_add (zneg c)))))
        (integerRing.symm (integerRing.sub_eq_add_neg a c))))

private theorem intFiniteSum_telescopes (a : Nat -> IntegerUp) :
    ∀ k : Nat,
      IntEq
        (intFiniteSum (fun m => zsub (a m) (a (Nat.succ m))) k)
        (zsub (a 0) (a (Nat.succ k)))
  | 0 => integerRing.refl (zsub (a 0) (a 1))
  | Nat.succ k => by
      exact integerRing.trans
        (integerRing.add_congr (intFiniteSum_telescopes a k)
          (integerRing.refl (zsub (a (Nat.succ k)) (a (Nat.succ (Nat.succ k))))))
        (zsub_add_zsub_cancel_middle (a 0) (a (Nat.succ k))
          (a (Nat.succ (Nat.succ k))))

private theorem lobbCoeff_zero_index (n : Nat) :
    IntEq
      (intOfNatStd (C (lobbTop n) (lobbLowerIndex 0 n)))
      (intOfNatStd (C (lobbTop n) n)) := by
  unfold lobbLowerIndex
  rw [Nat.add_zero]
  exact integerRing.refl (intOfNatStd (C (lobbTop n) n))

private theorem lobbCoeff_after_row_zero (n : Nat) :
    IntEq
      (intOfNatStd (C (lobbTop n) (lobbLowerIndex (Nat.succ n) n)))
      zzero := by
  unfold lobbTop lobbLowerIndex zzero intOfNatStd
  rw [Nat.add_succ]
  have above :
      C (n + n) (Nat.succ (n + n)) = 0 := by
    have raw := BEDC.Derived.BinomialIdentitiesUp.binomial_above (n + n) 0
    rw [Nat.add_zero] at raw
    exact raw
  rw [above]
  exact integerRing.refl zzero

theorem lobbNat_zero_left (n : Nat) :
    lobbNat 0 n = catalanNat n := by
  unfold lobbNat catalanNat lobbLowerIndex lobbUpperIndex
  rw [Nat.add_zero]

theorem lobbInteger_zero_left (n : Nat) :
    IntEq (lobbInteger 0 n) (catalanInteger n) := by
  unfold lobbInteger catalanInteger lobbLowerIndex lobbUpperIndex
  rw [Nat.add_zero]
  exact integerRing.refl
    (zsub (intOfNatStd (C (lobbTop n) n))
      (intOfNatStd (C (lobbTop n) (Nat.succ n))))

theorem lobbInteger_is_bedc_integer (m n : Nat) :
    BEDC.Derived.IntUp.IntPairCarrier
      (BEDC.Derived.RationalUp.intToPair (lobbInteger m n)).1
      (BEDC.Derived.RationalUp.intToPair (lobbInteger m n)).2 := by
  exact BEDC.Derived.RationalUp.intToPair_carrier (lobbInteger m n)

theorem lobbRowSumInteger_telescopes (n : Nat) :
    IntEq (lobbRowSumInteger n)
      (zsub
        (intOfNatStd (C (lobbTop n) (lobbLowerIndex 0 n)))
        (intOfNatStd (C (lobbTop n) (lobbLowerIndex (Nat.succ n) n)))) := by
  unfold lobbRowSumInteger lobbInteger lobbUpperIndex
  exact intFiniteSum_telescopes
    (fun m => intOfNatStd (C (lobbTop n) (lobbLowerIndex m n))) n

theorem lobbRowSumInteger_central_binomial (n : Nat) :
    IntEq (lobbRowSumInteger n) (lobbCentralBinomialInteger n) := by
  exact integerRing.trans
    (lobbRowSumInteger_telescopes n)
    (integerRing.trans
      (zsub_congr (lobbCoeff_zero_index n) (lobbCoeff_after_row_zero n))
      (zsub_zero_right (intOfNatStd (C (lobbTop n) n))))

theorem lobbRowSumInteger_closed (n : Nat) :
    BEDC.Derived.IntUp.IntPairCarrier
      (BEDC.Derived.RationalUp.intToPair (lobbRowSumInteger n)).1
      (BEDC.Derived.RationalUp.intToPair (lobbRowSumInteger n)).2 := by
  exact BEDC.Derived.RationalUp.intToPair_carrier (lobbRowSumInteger n)

theorem catalanNat_small_values :
    catalanNat 0 = 1 ∧ catalanNat 1 = 1 ∧
      catalanNat 2 = 2 ∧ catalanNat 3 = 5 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem catalanNat_agrees_with_CatalanUp_small_values :
    BEDC.Derived.CatalanUp.Catalan BHist.Empty (natToUnary (catalanNat 0)) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 1) (natToUnary (catalanNat 1)) ∧
        BEDC.Derived.CatalanUp.Catalan (natToUnary 2) (natToUnary (catalanNat 2)) ∧
          BEDC.Derived.CatalanUp.Catalan (natToUnary 3) (natToUnary (catalanNat 3)) := by
  constructor
  · exact BEDC.Derived.CatalanUp.catalan_zero
  · constructor
    · exact BEDC.Derived.CatalanUp.catalan_one
    · constructor
      · exact BEDC.Derived.CatalanUp.catalan_two
      · exact BEDC.Derived.CatalanUp.catalan_three

theorem LobbUp_constructive_export :
    (∀ n : Nat, lobbNat 0 n = catalanNat n) ∧
      (∀ n : Nat, IntEq (lobbInteger 0 n) (catalanInteger n)) ∧
        (∀ n : Nat,
          IntEq (lobbRowSumInteger n) (lobbCentralBinomialInteger n)) ∧
          (∀ m n : Nat,
            BEDC.Derived.IntUp.IntPairCarrier
              (BEDC.Derived.RationalUp.intToPair (lobbInteger m n)).1
              (BEDC.Derived.RationalUp.intToPair (lobbInteger m n)).2) := by
  constructor
  · intro n
    exact lobbNat_zero_left n
  · constructor
    · intro n
      exact lobbInteger_zero_left n
    · constructor
      · intro n
        exact lobbRowSumInteger_central_binomial n
      · intro m n
        exact lobbInteger_is_bedc_integer m n

end BEDC.Derived.LobbUp
