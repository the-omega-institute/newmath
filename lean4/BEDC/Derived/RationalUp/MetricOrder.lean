import BEDC.Derived.RationalUp.FieldLaws
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.RationalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (pairLe intLt natLeBool pairLe_of_length_order
  pairLe_total pairLe_antisymm_classifier intLt_to_pairLe pairLe_iff_length_order
  IntPairCarrier)

def ratSub (x y : RatNum) : RatNum :=
  ratAdd x (ratNeg y)

abbrev RatInt : Type :=
  BEDC.Derived.PrimeUp.IntegerUp

def intLe (x y : RatInt) : Prop :=
  pairLe (intToPair x) (intToPair y)

def intLtUp (x y : RatInt) : Prop :=
  intLt (intToPair x) (intToPair y)

def ratLe (x y : RatNum) : Prop :=
  intLe
    (IntMul x.num (ratDenInt y))
    (IntMul y.num (ratDenInt x))

def ratLt (x y : RatNum) : Prop :=
  intLtUp
    (IntMul x.num (ratDenInt y))
    (IntMul y.num (ratDenInt x))

def ratLeBool (x y : RatNum) : Bool :=
  natLeBool
    (bwordLength
        (intToPair (IntMul x.num (ratDenInt y))).1 +
      bwordLength
        (intToPair (IntMul y.num (ratDenInt x))).2)
    (bwordLength
        (intToPair (IntMul y.num (ratDenInt x))).1 +
      bwordLength
        (intToPair (IntMul x.num (ratDenInt y))).2)

def ratLtBool (x y : RatNum) : Bool :=
  natLeBool
    (Nat.succ
      (bwordLength
          (intToPair (IntMul x.num (ratDenInt y))).1 +
        bwordLength
          (intToPair (IntMul y.num (ratDenInt x))).2))
    (bwordLength
        (intToPair (IntMul y.num (ratDenInt x))).1 +
      bwordLength
        (intToPair (IntMul x.num (ratDenInt y))).2)

def ratAbs (x : RatNum) : RatNum :=
  ratMagnitude x

def ratDist (x y : RatNum) : RatNum :=
  ratAbs (ratSub x y)

theorem intLe_refl (x : RatInt) :
    intLe x x := by
  unfold intLe
  exact pairLe_of_length_order (intToPair_carrier x) (intToPair_carrier x)
    (Nat.le_refl _)

theorem intLe_total (x y : RatInt) :
    intLe x y ∨ intLe y x := by
  unfold intLe
  exact pairLe_total (intToPair_carrier x) (intToPair_carrier y)

theorem intLe_antisymm {x y : RatInt} :
    intLe x y -> intLe y x -> IntEq x y := by
  intro xy yx
  unfold intLe at xy yx
  unfold IntEq
  exact pairLe_antisymm_classifier (intToPair_carrier x) (intToPair_carrier y) xy yx

private theorem nat_add_four_last_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + d) + (c + b) := by
  calc
    (a + b) + (c + d) = (a + b) + (d + c) :=
      congrArg (fun t => (a + b) + t) (Nat.add_comm c d)
    _ = a + (b + (d + c)) := Nat.add_assoc a b (d + c)
    _ = a + ((b + d) + c) := congrArg (fun t => a + t) (Nat.add_assoc b d c).symm
    _ = a + ((d + b) + c) := congrArg (fun t => a + (t + c)) (Nat.add_comm b d)
    _ = a + (d + (b + c)) := congrArg (fun t => a + t) (Nat.add_assoc d b c)
    _ = (a + d) + (b + c) := (Nat.add_assoc a d (b + c)).symm
    _ = (a + d) + (c + b) := congrArg (fun t => (a + d) + t) (Nat.add_comm b c)

private theorem nat_le_cancel_add_right {a b c : Nat} :
    a + c ≤ b + c -> a ≤ b := by
  induction c with
  | zero =>
      intro h
      rw [Nat.add_zero] at h
      rw [Nat.add_zero] at h
      exact h
  | succ c ih =>
      intro h
      rw [Nat.add_succ] at h
      rw [Nat.add_succ] at h
      exact ih (Nat.le_of_succ_le_succ h)

theorem intLe_trans {x y z : RatInt} :
    intLe x y -> intLe y z -> intLe x z := by
  intro xy yz
  unfold intLe at xy yz ⊢
  have hx := intToPair_carrier x
  have hy := intToPair_carrier y
  have hz := intToPair_carrier z
  have xyLen := (pairLe_iff_length_order hx hy).mp xy
  have yzLen := (pairLe_iff_length_order hy hz).mp yz
  apply pairLe_of_length_order hx hz
  have combined :
      (bwordLength (intToPair x).1 + bwordLength (intToPair y).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair z).2) ≤
        (bwordLength (intToPair y).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair z).1 + bwordLength (intToPair y).2) :=
    Nat.add_le_add xyLen yzLen
  have rearranged :
      (bwordLength (intToPair x).1 + bwordLength (intToPair z).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) ≤
        (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) := by
    calc
      (bwordLength (intToPair x).1 + bwordLength (intToPair z).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2)
          =
        (bwordLength (intToPair x).1 + bwordLength (intToPair y).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair z).2) := by
            exact (nat_add_four_last_swap
              (bwordLength (intToPair x).1)
              (bwordLength (intToPair y).2)
              (bwordLength (intToPair y).1)
              (bwordLength (intToPair z).2)).symm
      _ ≤
        (bwordLength (intToPair y).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair z).1 + bwordLength (intToPair y).2) :=
            combined
      _ =
        (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) +
          (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) := by
            calc
              (bwordLength (intToPair y).1 + bwordLength (intToPair x).2) +
                  (bwordLength (intToPair z).1 + bwordLength (intToPair y).2)
                  =
                (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) +
                  (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) := by
                    exact nat_add_four_last_swap
                      (bwordLength (intToPair y).1)
                      (bwordLength (intToPair x).2)
                      (bwordLength (intToPair z).1)
                      (bwordLength (intToPair y).2)
              _ =
                (bwordLength (intToPair z).1 + bwordLength (intToPair x).2) +
                  (bwordLength (intToPair y).1 + bwordLength (intToPair y).2) := by
                    exact Nat.add_comm
                      (bwordLength (intToPair y).1 + bwordLength (intToPair y).2)
                      (bwordLength (intToPair z).1 + bwordLength (intToPair x).2)
  exact nat_le_cancel_add_right rearranged

theorem intLt_to_intLe {x y : RatInt} :
    intLtUp x y -> intLe x y := by
  intro h
  change pairLe (intToPair x) (intToPair y)
  change intLt (intToPair x) (intToPair y) at h
  exact intLt_to_pairLe (intToPair_carrier x) (intToPair_carrier y) h

theorem ratLe_refl (x : RatNum) :
    ratLe x x := by
  unfold ratLe
  exact intLe_refl _

theorem ratLe_total (x y : RatNum) :
    ratLe x y ∨ ratLe y x := by
  unfold ratLe
  exact intLe_total _ _

theorem ratLt_to_ratLe {x y : RatNum} :
    ratLt x y -> ratLe x y := by
  intro h
  change intLe (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x))
  change intLtUp (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)) at h
  exact intLt_to_intLe h

theorem ratLe_antisymm {x y : RatNum} :
    ratLe x y -> ratLe y x -> RatEq x y := by
  intro xy yx
  unfold ratLe at xy yx
  unfold RatEq
  exact intLe_antisymm xy yx

theorem ratAbs_eq_magnitude (x : RatNum) :
    RatEq (ratAbs x) (ratMagnitude x) := by
  exact RatEq_refl _

theorem ratDist_eq_abs_sub (x y : RatNum) :
    RatEq (ratDist x y) (ratAbs (ratSub x y)) := by
  exact RatEq_refl _

theorem ratLe_decidable (x y : RatNum) :
    ratLe x y ∨ (ratLe x y -> False) := by
  unfold ratLe intLe
  let left := intToPair (IntMul x.num (ratDenInt y))
  let right := intToPair (IntMul y.num (ratDenInt x))
  have leftCarrier : IntPairCarrier left.1 left.2 := by
    unfold left
    exact intToPair_carrier _
  have rightCarrier : IntPairCarrier right.1 right.2 := by
    unfold right
    exact intToPair_carrier _
  by_cases h :
      bwordLength left.1 + bwordLength right.2 ≤
        bwordLength right.1 + bwordLength left.2
  · exact Or.inl (pairLe_of_length_order leftCarrier rightCarrier h)
  · exact Or.inr (fun leProof =>
      h ((pairLe_iff_length_order leftCarrier rightCarrier).mp leProof))

theorem ratNeg_respects {x y : RatNum} :
    RatEq x y -> RatEq (ratNeg x) (ratNeg y) := by
  intro h
  unfold RatEq at h
  unfold RatEq ratNeg
  have left :
      IntEq
        (IntMul (IntNeg x.num) (ratDenInt y))
        (IntNeg (IntMul x.num (ratDenInt y))) :=
    BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt y)
  have middle :
      IntEq
        (IntNeg (IntMul x.num (ratDenInt y)))
        (IntNeg (IntMul y.num (ratDenInt x))) :=
    IntNeg_respects h
  have right :
      IntEq
        (IntNeg (IntMul y.num (ratDenInt x)))
        (IntMul (IntNeg y.num) (ratDenInt x)) :=
    IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x))
  exact IntEq_trans left (IntEq_trans middle right)

private theorem intMul_cross_four {a b a' b' c d : RatInt} :
    IntEq (IntMul a b) (IntMul a' b') ->
      IntEq (IntMul (IntMul a c) (IntMul b d))
        (IntMul (IntMul a' d) (IntMul b' c)) := by
  intro h
  exact IntEq_trans (intMul_two_by_two_swap a c b d)
    (IntEq_trans
      (intMul_right_congr h)
      (IntEq_trans
        (intMul_left_congr (c := IntMul a' b') (IntMul_comm c d))
        (IntEq_symm (intMul_two_by_two_swap a' d b' c))))

private theorem intMul_cross_four_right {a b a' b' c d : RatInt} :
    IntEq (IntMul a b) (IntMul a' b') ->
      IntEq (IntMul (IntMul a c) (IntMul d b))
        (IntMul (IntMul a' d) (IntMul c b')) := by
  intro h
  exact IntEq_trans
    (intMul_left_congr (c := IntMul a c) (IntMul_comm d b))
    (IntEq_trans
      (intMul_cross_four (a := a) (b := b) (a' := a') (b' := b') (c := c) (d := d) h)
      (intMul_left_congr (c := IntMul a' d) (IntMul_comm b' c)))

theorem ratAdd_respects {x x' y y' : RatNum} :
    RatEq x x' -> RatEq y y' ->
      RatEq (ratAdd x y) (ratAdd x' y') := by
  intro xx' yy'
  unfold RatEq at xx' yy' ⊢
  change
    IntEq
      (IntMul
        (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
        (ratDenInt (ratAdd x' y')))
      (IntMul
        (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
        (ratDenInt (ratAdd x y)))
  have leftDen :
      IntEq (ratDenInt (ratAdd x' y'))
        (IntMul (ratDenInt x') (ratDenInt y')) :=
    ratDenInt_add x' y'
  have rightDen :
      IntEq (ratDenInt (ratAdd x y))
        (IntMul (ratDenInt x) (ratDenInt y)) :=
    ratDenInt_add x y
  have leftToStructured :
      IntEq
        (IntMul
          (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
          (ratDenInt (ratAdd x' y')))
        (IntMul
          (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
          (IntMul (ratDenInt x') (ratDenInt y'))) :=
    intMul_left_congr leftDen
  have rightToStructured :
      IntEq
        (IntMul
          (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
          (ratDenInt (ratAdd x y)))
        (IntMul
          (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
          (IntMul (ratDenInt x) (ratDenInt y))) :=
    intMul_left_congr rightDen
  have firstTerm :
      IntEq
        (IntMul (IntMul x.num (ratDenInt y))
          (IntMul (ratDenInt x') (ratDenInt y')))
        (IntMul (IntMul x'.num (ratDenInt y'))
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact intMul_cross_four
      (a := x.num) (b := ratDenInt x') (a' := x'.num) (b' := ratDenInt x)
      (c := ratDenInt y) (d := ratDenInt y') xx'
  have secondTerm :
      IntEq
        (IntMul (IntMul y.num (ratDenInt x))
          (IntMul (ratDenInt x') (ratDenInt y')))
        (IntMul (IntMul y'.num (ratDenInt x'))
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact intMul_cross_four_right
      (a := y.num) (b := ratDenInt y') (a' := y'.num) (b' := ratDenInt y)
      (c := ratDenInt x) (d := ratDenInt x') yy'
  have structured :
      IntEq
        (IntMul
          (IntAdd (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x)))
          (IntMul (ratDenInt x') (ratDenInt y')))
        (IntMul
          (IntAdd (IntMul x'.num (ratDenInt y')) (IntMul y'.num (ratDenInt x')))
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact IntEq_trans
      (IntMul_add_distrib_right (IntMul x.num (ratDenInt y))
        (IntMul y.num (ratDenInt x))
        (IntMul (ratDenInt x') (ratDenInt y')))
      (IntEq_trans
        (IntAdd_respects firstTerm secondTerm)
        (IntEq_symm
          (IntMul_add_distrib_right (IntMul x'.num (ratDenInt y'))
            (IntMul y'.num (ratDenInt x'))
            (IntMul (ratDenInt x) (ratDenInt y)))))
  exact IntEq_trans leftToStructured
    (IntEq_trans structured (IntEq_symm rightToStructured))

def ratHalf : RatNum :=
  { num := intOne
    den := BHist.e1 BEDC.Derived.PadicUp.NatOne
    den_pos :=
      Or.inl
        ⟨BEDC.Derived.PadicUp.NatOne, unary_e1_closed unary_empty,
          BEDC.FKernel.Hist.not_hsame_e1_empty, rfl⟩ }

def ratMidpoint (x y : RatNum) : RatNum :=
  ratMul (ratAdd x y) ratHalf

structure RatDenseBetween (x y : RatNum) where
  point : RatNum
  left : ratLt x point
  right : ratLt point y

end BEDC.Derived.RationalUp
