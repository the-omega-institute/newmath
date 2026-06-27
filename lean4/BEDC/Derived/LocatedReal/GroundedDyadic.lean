import BEDC.Derived.LocatedReal.ToleranceClose

namespace BEDC.Derived.LocatedReal

open BEDC.Derived.RationalUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)

private abbrev RatInt : Type :=
  BEDC.Derived.PrimeUp.IntegerUp

theorem natToUnary_append_eq (m n : Nat) :
    BEDC.FKernel.Cont.append
      (BEDC.Derived.IntUp.natToUnary m)
      (BEDC.Derived.IntUp.natToUnary n) =
        BEDC.Derived.IntUp.natToUnary (m + n) := by
  induction n with
  | zero =>
      exact BEDC.FKernel.Cont.append_empty_right
        (BEDC.Derived.IntUp.natToUnary m)
  | succ n ih =>
      change
        BHist.e1
          (BEDC.FKernel.Cont.append
            (BEDC.Derived.IntUp.natToUnary m)
            (BEDC.Derived.IntUp.natToUnary n)) =
          BEDC.Derived.IntUp.natToUnary (m + Nat.succ n)
      rw [ih, Nat.add_succ]
      rfl

theorem natMulFn_natToUnary_eq (m n : Nat) :
    BEDC.Derived.IntUp.natMulFn
      (BEDC.Derived.IntUp.natToUnary m)
      (BEDC.Derived.IntUp.natToUnary n) =
        BEDC.Derived.IntUp.natToUnary (m * n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        BEDC.FKernel.Cont.append
          (BEDC.Derived.IntUp.natMulFn
            (BEDC.Derived.IntUp.natToUnary m)
            (BEDC.Derived.IntUp.natToUnary n))
          (BEDC.Derived.IntUp.natToUnary m) =
            BEDC.Derived.IntUp.natToUnary (m * Nat.succ n)
      rw [ih, natToUnary_append_eq]
      exact congrArg BEDC.Derived.IntUp.natToUnary (Nat.mul_succ m n)

theorem powTwoNat_succ (k : Nat) :
    powTwoNat (Nat.succ k) = 2 * powTwoNat k := by
  rfl

private theorem nat_right_distrib_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.left_distrib c a b
    _ = a * c + c * b := congrArg (fun t => t + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun t => a * c + t) (Nat.mul_comm c b)

private def intNat (n : Nat) : RatInt :=
  intOfNat (BEDC.Derived.IntUp.natToUnary n)
    (BEDC.Derived.IntUp.natToUnary_unary n)

private theorem intOne_eq_intNat_one :
    IntEq intOne (intNat 1) := by
  unfold intNat intOne BEDC.Derived.PadicUp.NatOne
  exact IntEq_refl _

theorem intOfNat_le_of_nat_le
    (a b : BHist) (ha : UnaryHistory a) (hb : UnaryHistory b) :
    bwordLength a <= bwordLength b ->
      intLe (intOfNat a ha) (intOfNat b hb) := by
  intro h
  unfold intLe intOfNat intToPair
  apply BEDC.Derived.IntUp.pairLe_of_length_order
  · exact ⟨ha, unary_empty⟩
  · exact ⟨hb, unary_empty⟩
  change bwordLength a <= bwordLength b + 0
  rw [Nat.add_zero]
  exact h

theorem intNat_add (a b : Nat) :
    IntEq (IntAdd (intNat a) (intNat b)) (intNat (a + b)) := by
  unfold intNat IntAdd intAdd intOfNat IntEq intToPair
  change
    BEDC.Derived.IntUp.IntPairClassifier
      (intToPair
        (pairToInt
          (BEDC.Derived.IntUp.pairAdd
            (BEDC.Derived.IntUp.natToUnary a, BHist.Empty)
            (BEDC.Derived.IntUp.natToUnary b, BHist.Empty))))
      (BEDC.Derived.IntUp.natToUnary (a + b), BHist.Empty)
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intToPair_pairToInt_classifier
      (BEDC.Derived.IntUp.pairAdd
        (BEDC.Derived.IntUp.natToUnary a, BHist.Empty)
        (BEDC.Derived.IntUp.natToUnary b, BHist.Empty))
      (BEDC.Derived.IntUp.pairAdd_carrier
        ⟨BEDC.Derived.IntUp.natToUnary_unary a, unary_empty⟩
        ⟨BEDC.Derived.IntUp.natToUnary_unary b, unary_empty⟩))
    (by
      apply IntPairClassifier_of_length_eq
      · exact BEDC.Derived.IntUp.pairAdd_carrier
          ⟨BEDC.Derived.IntUp.natToUnary_unary a, unary_empty⟩
          ⟨BEDC.Derived.IntUp.natToUnary_unary b, unary_empty⟩
      · exact ⟨BEDC.Derived.IntUp.natToUnary_unary (a + b), unary_empty⟩
      unfold BEDC.Derived.IntUp.pairAdd
      rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
      rw [BEDC.Derived.IntUp.natToUnary_length]
      rw [BEDC.Derived.IntUp.natToUnary_length]
      rw [BEDC.Derived.IntUp.natToUnary_length]
      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
      change a + b + 0 = a + b + 0
      rfl)

theorem intNat_mul (a b : Nat) :
    IntEq (IntMul (intNat a) (intNat b)) (intNat (a * b)) := by
  unfold intNat
  have raw :=
    intOfNat_natMul_as_intMul
      (BEDC.Derived.IntUp.natToUnary a)
      (BEDC.Derived.IntUp.natToUnary b)
      (BEDC.Derived.IntUp.natToUnary_unary a)
      (BEDC.Derived.IntUp.natToUnary_unary b)
      (BEDC.Derived.IntUp.natMulFn_unary
        (BEDC.Derived.IntUp.natToUnary_unary a)
        (BEDC.Derived.IntUp.natToUnary_unary b))
  exact IntEq_trans (IntEq_symm raw)
    (by
      exact intOfNat_hsame_congr
        (BEDC.Derived.IntUp.natMulFn_unary
          (BEDC.Derived.IntUp.natToUnary_unary a)
          (BEDC.Derived.IntUp.natToUnary_unary b))
        (BEDC.Derived.IntUp.natToUnary_unary (a * b))
        (natMulFn_natToUnary_eq a b))

theorem ratDenInt_dyadic (k : Nat) :
    IntEq (ratDenInt (dyadicRat k)) (intNat (powTwoNat k)) := by
  unfold ratDenInt dyadicRat intNat
  exact IntEq_refl _

theorem dyadic_add_num (k : Nat) :
    IntEq (ratAdd (dyadicRat k) (dyadicRat k)).num
      (intNat (powTwoNat k + powTwoNat k)) := by
  unfold ratAdd
  change
    IntEq
      (IntAdd
        (IntMul (dyadicRat k).num (ratDenInt (dyadicRat k)))
        (IntMul (dyadicRat k).num (ratDenInt (dyadicRat k))))
      (intNat (powTwoNat k + powTwoNat k))
  have term :
      IntEq (IntMul (dyadicRat k).num (ratDenInt (dyadicRat k)))
        (intNat (powTwoNat k)) := by
    exact IntEq_trans
      (IntMul_respects intOne_eq_intNat_one (ratDenInt_dyadic k))
      (IntEq_trans (intNat_mul 1 (powTwoNat k))
        (by
          change IntEq (intNat (1 * powTwoNat k)) (intNat (powTwoNat k))
          rw [Nat.one_mul]
          exact IntEq_refl _))
  exact IntEq_trans (IntAdd_respects term term)
    (intNat_add (powTwoNat k) (powTwoNat k))

theorem dyadic_add_den (k : Nat) :
    IntEq (ratDenInt (ratAdd (dyadicRat k) (dyadicRat k)))
      (intNat (powTwoNat k * powTwoNat k)) := by
  exact IntEq_trans (ratDenInt_add (dyadicRat k) (dyadicRat k))
    (IntEq_trans
      (IntMul_respects (ratDenInt_dyadic k) (ratDenInt_dyadic k))
      (intNat_mul (powTwoNat k) (powTwoNat k)))

theorem dyadic_succ_nat_bound (k : Nat) :
    (powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) * powTwoNat k <=
      powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k) := by
  change (2 * powTwoNat k + 2 * powTwoNat k) * powTwoNat k <=
    (2 * powTwoNat k) * (2 * powTwoNat k)
  have twoE : 2 * powTwoNat k = powTwoNat k + powTwoNat k :=
    Nat.two_mul (powTwoNat k)
  exact Nat.le_of_eq
    (calc
      (2 * powTwoNat k + 2 * powTwoNat k) * powTwoNat k =
          (2 * powTwoNat k) * powTwoNat k +
            (2 * powTwoNat k) * powTwoNat k := nat_right_distrib_clean _ _ _
      _ = (2 * powTwoNat k) * (powTwoNat k + powTwoNat k) :=
          (Nat.left_distrib (2 * powTwoNat k) (powTwoNat k) (powTwoNat k)).symm
      _ = (2 * powTwoNat k) * (2 * powTwoNat k) :=
          congrArg (fun t => (2 * powTwoNat k) * t) twoE.symm)

theorem dyadic_succ_add (k : Nat) :
    ratLe (ratAdd (dyadicRat (Nat.succ k)) (dyadicRat (Nat.succ k)))
      (dyadicRat k) := by
  unfold ratLe
  have leftNorm :
      IntEq
        (IntMul (ratAdd (dyadicRat (Nat.succ k)) (dyadicRat (Nat.succ k))).num
          (ratDenInt (dyadicRat k)))
        (intNat ((powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) * powTwoNat k)) := by
    exact IntEq_trans
      (IntMul_respects (dyadic_add_num (Nat.succ k)) (ratDenInt_dyadic k))
      (intNat_mul (powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) (powTwoNat k))
  have rightNorm :
      IntEq
        (IntMul (dyadicRat k).num
          (ratDenInt (ratAdd (dyadicRat (Nat.succ k)) (dyadicRat (Nat.succ k)))))
        (intNat (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k))) := by
    exact IntEq_trans
      (IntMul_respects intOne_eq_intNat_one (dyadic_add_den (Nat.succ k)))
      (IntEq_trans (intNat_mul 1 (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k)))
        (by
          change IntEq
            (intNat (1 * (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k))))
            (intNat (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k)))
          rw [Nat.one_mul]
          exact IntEq_refl _))
  exact intLe_respects (IntEq_symm leftNorm) (IntEq_symm rightNorm)
    (intOfNat_le_of_nat_le
      (BEDC.Derived.IntUp.natToUnary
        ((powTwoNat (Nat.succ k) + powTwoNat (Nat.succ k)) * powTwoNat k))
      (BEDC.Derived.IntUp.natToUnary
        (powTwoNat (Nat.succ k) * powTwoNat (Nat.succ k)))
      (BEDC.Derived.IntUp.natToUnary_unary _)
      (BEDC.Derived.IntUp.natToUnary_unary _)
      (by
        rw [BEDC.Derived.IntUp.natToUnary_length,
          BEDC.Derived.IntUp.natToUnary_length]
        exact dyadic_succ_nat_bound k))

end BEDC.Derived.LocatedReal
