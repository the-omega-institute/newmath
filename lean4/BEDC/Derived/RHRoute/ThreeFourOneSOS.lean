import BEDC.Derived.RHRoute.JensenTuranDegree2

namespace BEDC.Derived.RHRoute.ThreeFourOneSOS

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp

abbrev Rat : Type :=
  RatNum

def natRat (n : Nat) : Rat :=
  BEDC.Real.RatNumKernel.ratNat n

def threeFourOneCosForm (c : Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratAdd (natRat 3) (ratMul (natRat 4) c))
      (ratMul (natRat 2) (ratMul c c)))
    (ratNeg ratOne)

def threeFourOneSOS (c : Rat) : Rat :=
  ratMul (natRat 2) (ratMul (ratAdd ratOne c) (ratAdd ratOne c))

private def threeFourOneNormal (c : Rat) : Rat :=
  ratAdd
    (ratAdd (natRat 2) (ratMul (natRat 4) c))
    (ratMul (natRat 2) (ratMul c c))

private theorem natRat_add (m n : Nat) :
    RatEq (ratAdd (natRat m) (natRat n)) (natRat (m + n)) := by
  unfold natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_add m n

private theorem natRat_one_eq :
    RatEq (natRat 1) ratOne := by
  unfold natRat BEDC.Real.RatNumKernel.ratNat ratOne intToRat intOne intOfNat
  exact RatEq_refl _

private theorem ratAdd_assoc (x y z : Rat) :
    RatEq (ratAdd (ratAdd x y) z) (ratAdd x (ratAdd y z)) :=
  BEDC.Derived.LocatedReal.ratAdd_assoc_local x y z

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

private theorem add_right_comm (x y z : Rat) :
    RatEq (ratAdd (ratAdd x y) z) (ratAdd (ratAdd x z) y) := by
  exact RatEq_trans _ _ _
    (ratAdd_assoc x y z)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x) (ratAdd_comm y z))
      (RatEq_symm (ratAdd_assoc x z y)))

private theorem add_four_move_last_to_second (a b c d : Rat) :
    RatEq
      (ratAdd (ratAdd (ratAdd a b) c) d)
      (ratAdd (ratAdd (ratAdd a d) b) c) := by
  exact RatEq_trans _ _ _
    (ratAdd_assoc (ratAdd a b) c d)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl (ratAdd a b)) (ratAdd_comm c d))
      (RatEq_trans _ _ _
        (RatEq_symm (ratAdd_assoc (ratAdd a b) d c))
        (ratAdd_respects (add_right_comm a b d) (RatEq_refl c))))

private theorem three_add_neg_one_eq_two :
    RatEq (ratAdd (natRat 3) (ratNeg ratOne)) (natRat 2) := by
  have oneAsNat : RatEq ratOne (natRat 1) :=
    RatEq_symm natRat_one_eq
  have twoPlusOne :
      RatEq (ratAdd (natRat 2) ratOne) (natRat 3) := by
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl (natRat 2)) oneAsNat)
      (natRat_add 2 1)
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_symm twoPlusOne) (RatEq_refl (ratNeg ratOne)))
    (RatEq_trans _ _ _
      (ratAdd_assoc (natRat 2) ratOne (ratNeg ratOne))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl (natRat 2))
          (BEDC.Derived.LocatedReal.ratAdd_neg_local ratOne))
        (ratAdd_zero_right (natRat 2))))

private theorem two_mul_add_self (c : Rat) :
    RatEq
      (ratMul (natRat 2) (ratAdd c c))
      (ratMul (natRat 4) c) := by
  have distribute :
      RatEq
        (ratMul (natRat 2) (ratAdd c c))
        (ratAdd (ratMul (natRat 2) c) (ratMul (natRat 2) c)) :=
    BEDC.Real.RatNumKernel.ratMul_add_left (natRat 2) c c
  have collect :
      RatEq
        (ratAdd (ratMul (natRat 2) c) (ratMul (natRat 2) c))
        (ratMul (ratAdd (natRat 2) (natRat 2)) c) :=
    RatEq_symm (BEDC.Real.RatNumKernel.ratMul_add_right
      (natRat 2) (natRat 2) c)
  have coeff :
      RatEq
        (ratMul (ratAdd (natRat 2) (natRat 2)) c)
        (ratMul (natRat 4) c) :=
    ratMul_respects (natRat_add 2 2) (RatEq_refl c)
  exact RatEq_trans _ _ _ distribute
    (RatEq_trans _ _ _ collect coeff)

private theorem one_plus_square_expand (c : Rat) :
    RatEq
      (ratMul (ratAdd ratOne c) (ratAdd ratOne c))
      (ratAdd (ratAdd ratOne (ratAdd c c)) (ratMul c c)) := by
  have firstDist :
      RatEq
        (ratMul (ratAdd ratOne c) (ratAdd ratOne c))
        (ratAdd
          (ratMul ratOne (ratAdd ratOne c))
          (ratMul c (ratAdd ratOne c))) :=
    BEDC.Real.RatNumKernel.ratMul_add_right ratOne c (ratAdd ratOne c)
  have firstSimplified :
      RatEq
        (ratAdd
          (ratMul ratOne (ratAdd ratOne c))
          (ratMul c (ratAdd ratOne c)))
        (ratAdd (ratAdd ratOne c) (ratAdd c (ratMul c c))) := by
    have rightDist :
        RatEq
          (ratMul c (ratAdd ratOne c))
          (ratAdd (ratMul c ratOne) (ratMul c c)) :=
      BEDC.Real.RatNumKernel.ratMul_add_left c ratOne c
    exact ratAdd_respects
      (ratOne_mul_left (ratAdd ratOne c))
      (RatEq_trans _ _ _ rightDist
        (ratAdd_respects (ratMul_one_right c) (RatEq_refl (ratMul c c))))
  have reassociate :
      RatEq
        (ratAdd (ratAdd ratOne c) (ratAdd c (ratMul c c)))
        (ratAdd (ratAdd ratOne (ratAdd c c)) (ratMul c c)) := by
    exact RatEq_trans _ _ _
      (ratAdd_assoc ratOne c (ratAdd c (ratMul c c)))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl ratOne)
          (RatEq_symm (ratAdd_assoc c c (ratMul c c))))
        (RatEq_symm (ratAdd_assoc ratOne (ratAdd c c) (ratMul c c))))
  exact RatEq_trans _ _ _ firstDist
    (RatEq_trans _ _ _ firstSimplified reassociate)

private theorem two_mul_expanded_square (c : Rat) :
    RatEq
      (ratMul (natRat 2)
        (ratAdd (ratAdd ratOne (ratAdd c c)) (ratMul c c)))
      (threeFourOneNormal c) := by
  have topDist :
      RatEq
        (ratMul (natRat 2)
          (ratAdd (ratAdd ratOne (ratAdd c c)) (ratMul c c)))
        (ratAdd
          (ratMul (natRat 2) (ratAdd ratOne (ratAdd c c)))
          (ratMul (natRat 2) (ratMul c c))) :=
    BEDC.Real.RatNumKernel.ratMul_add_left
      (natRat 2) (ratAdd ratOne (ratAdd c c)) (ratMul c c)
  have headDist :
      RatEq
        (ratMul (natRat 2) (ratAdd ratOne (ratAdd c c)))
        (ratAdd (natRat 2) (ratMul (natRat 4) c)) := by
    have raw :
        RatEq
          (ratMul (natRat 2) (ratAdd ratOne (ratAdd c c)))
          (ratAdd
            (ratMul (natRat 2) ratOne)
            (ratMul (natRat 2) (ratAdd c c))) :=
      BEDC.Real.RatNumKernel.ratMul_add_left
        (natRat 2) ratOne (ratAdd c c)
    exact RatEq_trans _ _ _ raw
      (ratAdd_respects (ratMul_one_right (natRat 2)) (two_mul_add_self c))
  unfold threeFourOneNormal
  exact RatEq_trans _ _ _ topDist
    (ratAdd_respects headDist (RatEq_refl (ratMul (natRat 2) (ratMul c c))))

private theorem sos_expands_to_normal (c : Rat) :
    RatEq (threeFourOneSOS c) (threeFourOneNormal c) := by
  unfold threeFourOneSOS
  exact RatEq_trans _ _ _
    (ratMul_respects (RatEq_refl (natRat 2)) (one_plus_square_expand c))
    (two_mul_expanded_square c)

private theorem cos_form_expands_to_normal (c : Rat) :
    RatEq (threeFourOneCosForm c) (threeFourOneNormal c) := by
  unfold threeFourOneCosForm threeFourOneNormal
  have reorder :
      RatEq
        (ratAdd
          (ratAdd
            (ratAdd (natRat 3) (ratMul (natRat 4) c))
            (ratMul (natRat 2) (ratMul c c)))
          (ratNeg ratOne))
        (ratAdd
          (ratAdd
            (ratAdd (natRat 3) (ratNeg ratOne))
            (ratMul (natRat 4) c))
          (ratMul (natRat 2) (ratMul c c))) :=
    add_four_move_last_to_second
      (natRat 3) (ratMul (natRat 4) c)
      (ratMul (natRat 2) (ratMul c c)) (ratNeg ratOne)
  exact RatEq_trans _ _ _ reorder
    (ratAdd_respects
      (ratAdd_respects three_add_neg_one_eq_two
        (RatEq_refl (ratMul (natRat 4) c)))
      (RatEq_refl (ratMul (natRat 2) (ratMul c c))))

theorem three_four_one_identity (c : Rat) :
    RatEq
      (ratAdd
        (ratAdd
          (ratAdd (natRat 3) (ratMul (natRat 4) c))
          (ratMul (natRat 2) (ratMul c c)))
        (ratNeg ratOne))
      (ratMul (natRat 2) (ratMul (ratAdd ratOne c) (ratAdd ratOne c))) := by
  change RatEq (threeFourOneCosForm c) (threeFourOneSOS c)
  exact RatEq_trans _ _ _
    (cos_form_expands_to_normal c)
    (RatEq_symm (sos_expands_to_normal c))

theorem two_one_plus_c_sq_nonneg (c : Rat) :
    ratLe ratZero
      (ratMul (natRat 2) (ratMul (ratAdd ratOne c) (ratAdd ratOne c))) := by
  change ratLe ratZero (threeFourOneSOS c)
  unfold threeFourOneSOS
  exact BEDC.Real.RatNumKernel.ratMul_nonneg
    (by
      unfold natRat
      exact BEDC.Real.RatNumKernel.ratNat_nonneg 2)
    (BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg
      (ratAdd ratOne c))

theorem cos_form_nonneg (c : Rat) :
    ratLe ratZero
      (ratAdd
        (ratAdd
          (ratAdd (natRat 3) (ratMul (natRat 4) c))
          (ratMul (natRat 2) (ratMul c c)))
        (ratNeg ratOne)) := by
  change ratLe ratZero (threeFourOneCosForm c)
  exact ratLe_respects
    (RatEq_refl ratZero)
    (RatEq_symm (three_four_one_identity c))
    (two_one_plus_c_sq_nonneg c)

private theorem sos_at_neg_one_zero :
    RatEq (threeFourOneSOS (ratNeg ratOne)) ratZero := by
  unfold threeFourOneSOS
  have oneCancel :
      RatEq (ratAdd ratOne (ratNeg ratOne)) ratZero :=
    BEDC.Derived.LocatedReal.ratAdd_neg_local ratOne
  exact RatEq_trans _ _ _
    (ratMul_respects (RatEq_refl (natRat 2))
      (ratMul_respects oneCancel oneCancel))
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (natRat 2))
        (ratMul_zero_left_local ratZero))
      (ratMul_zero_right_local (natRat 2)))

private theorem sos_at_zero_two :
    RatEq (threeFourOneSOS ratZero) (natRat 2) := by
  unfold threeFourOneSOS
  have onePlusZero :
      RatEq (ratAdd ratOne ratZero) ratOne :=
    ratAdd_zero_right ratOne
  exact RatEq_trans _ _ _
    (ratMul_respects (RatEq_refl (natRat 2))
      (ratMul_respects onePlusZero onePlusZero))
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (natRat 2))
        (ratOne_mul_left ratOne))
      (ratMul_one_right (natRat 2)))

example :
    RatEq
      (ratAdd
        (ratAdd
          (ratAdd (natRat 3) (ratMul (natRat 4) (ratNeg ratOne)))
          (ratMul (natRat 2) (ratMul (ratNeg ratOne) (ratNeg ratOne))))
        (ratNeg ratOne))
      ratZero := by
  change RatEq (threeFourOneCosForm (ratNeg ratOne)) ratZero
  exact RatEq_trans _ _ _
    (three_four_one_identity (ratNeg ratOne))
    sos_at_neg_one_zero

example :
    RatEq
      (ratAdd
        (ratAdd
          (ratAdd (natRat 3) (ratMul (natRat 4) ratZero))
          (ratMul (natRat 2) (ratMul ratZero ratZero)))
        (ratNeg ratOne))
      (natRat 2) := by
  change RatEq (threeFourOneCosForm ratZero) (natRat 2)
  exact RatEq_trans _ _ _
    (three_four_one_identity ratZero)
    sos_at_zero_two

end BEDC.Derived.RHRoute.ThreeFourOneSOS
