import BEDC.Algebra.FiniteFold
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

abbrev BRat : Type :=
  Rat

def natRat : Nat -> Rat
  | 0 => ratZero
  | 1 => ratOne
  | 2 => ratAdd ratOne ratOne
  | Nat.succ n => BEDC.Real.RatNumKernel.ratNat (Nat.succ n)

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

def ratRingCanonical : RelCommRing Rat RatEq where
  zero := ratZero
  one := ratOne
  add := ratAdd
  mul := ratMul
  neg := ratNeg
  refl := RatEq_refl
  symm := RatEq_symm
  trans := by
    intro _ _ _
    exact RatEq_trans _ _ _
  add_congr := by
    intro _ _ _ _ hleft hright
    exact ratAdd_respects hleft hright
  mul_congr := by
    intro _ _ _ _ hleft hright
    exact ratMul_respects hleft hright
  neg_congr := by
    intro _ _ h
    exact ratNeg_respects h
  add_assoc := BEDC.Derived.LocatedReal.ratAdd_assoc_local
  add_comm := ratAdd_comm
  add_zero := ratAdd_zero_right
  zero_add := ratZero_add_left
  add_neg := BEDC.Derived.LocatedReal.ratAdd_neg_local
  neg_add := BEDC.Derived.LocatedReal.ratNeg_add_local
  mul_assoc := ratMul_assoc
  mul_one := ratMul_one_right
  one_mul := ratOne_mul_left
  mul_zero := ratMul_zero_right_local
  zero_mul := ratMul_zero_left_local
  left_distrib := BEDC.Real.RatNumKernel.ratMul_add_left
  right_distrib := BEDC.Real.RatNumKernel.ratMul_add_right
  mul_comm := ratMul_comm

def bratRingCanonical : RelCommRing BRat RatEq where
  zero := ratZero
  one := ratOne
  add := ratAdd
  mul := ratMul
  neg := ratNeg
  refl := RatEq_refl
  symm := RatEq_symm
  trans := by
    intro _ _ _
    exact RatEq_trans _ _ _
  add_congr := by
    intro _ _ _ _ hleft hright
    exact ratAdd_respects hleft hright
  mul_congr := by
    intro _ _ _ _ hleft hright
    exact ratMul_respects hleft hright
  neg_congr := by
    intro _ _ h
    exact ratNeg_respects h
  add_assoc := BEDC.Derived.LocatedReal.ratAdd_assoc_local
  add_comm := ratAdd_comm
  add_zero := ratAdd_zero_right
  zero_add := ratZero_add_left
  add_neg := BEDC.Derived.LocatedReal.ratAdd_neg_local
  neg_add := BEDC.Derived.LocatedReal.ratNeg_add_local
  mul_assoc := ratMul_assoc
  mul_one := ratMul_one_right
  one_mul := ratOne_mul_left
  mul_zero := ratMul_zero_right_local
  zero_mul := ratMul_zero_left_local
  left_distrib := BEDC.Real.RatNumKernel.ratMul_add_left
  right_distrib := BEDC.Real.RatNumKernel.ratMul_add_right
  mul_comm := ratMul_comm

end BEDC.Derived.RHRoute.IntervalMatrixPSD
