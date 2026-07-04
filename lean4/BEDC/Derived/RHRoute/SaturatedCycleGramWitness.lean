import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# Saturated-cycle Gram witness

This is a finite negative witness for the golden/reflection-positivity cone:
a saturated carry cycle with nontrivial holonomy has a Gram matrix that is not
PSD in the concrete three-state signed holonomy `h = -1` case.

Boundary: this is not RH and it states no zeta-zero conclusion. It is only the
minimal finite certificate for the reflection-positivity classification mechanism
`holonomy != 1 => non-PSD`.
-/

namespace BEDC.Derived.RHRoute.SaturatedCycleGramWitness

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNum

/-- Local natural-number adapter whose small denominator-one literals reduce definitionally. -/
def natRat : Nat -> Rat
  | 0 => ratZero
  | 1 => ratOne
  | 2 => ratTwo
  | 4 => ratFour
  | Nat.succ n => BEDC.Real.RatNumKernel.ratNat (Nat.succ n)

def i0 : Fin 3 :=
  ⟨0, Nat.succ_pos 2⟩

def i1 : Fin 3 :=
  ⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩

def i2 : Fin 3 :=
  ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩

/-- The signed-holonomy `h = -1` three-cycle Gram matrix. -/
def G3 : Fin 3 -> Fin 3 -> Rat
  | ⟨0, _⟩, ⟨2, _⟩ => ratNeg ratOne
  | ⟨2, _⟩, ⟨0, _⟩ => ratNeg ratOne
  | _, _ => ratOne

/-- The negative direction `(1, -2, 1)`. -/
def w3 : Fin 3 -> Rat
  | ⟨0, _⟩ => ratOne
  | ⟨1, _⟩ => ratNeg ratTwo
  | ⟨2, _⟩ => ratOne
  | _ => ratZero

def qterm (M : Fin 3 -> Fin 3 -> Rat) (v : Fin 3 -> Rat)
    (i j : Fin 3) : Rat :=
  ratMul (ratMul (v i) (M i j)) (v j)

/-- Explicit finite double sum for the three-state quadratic form. -/
def quadForm3 (M : Fin 3 -> Fin 3 -> Rat) (v : Fin 3 -> Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratAdd (qterm M v i0 i0) (qterm M v i0 i1))
      (ratAdd (qterm M v i0 i2) (qterm M v i1 i0)))
    (ratAdd
      (ratAdd (qterm M v i1 i1) (qterm M v i1 i2))
      (ratAdd (qterm M v i2 i0)
        (ratAdd (qterm M v i2 i1) (qterm M v i2 i2))))

/-- The displayed scalar `w^T G w`, reduced through `G w = (-2, 0, -2)`. -/
def qf3 : Rat :=
  ratAdd
    (ratAdd
      (ratMul (w3 i0) (ratNeg ratTwo))
      (ratMul (w3 i1) ratZero))
    (ratMul (w3 i2) (ratNeg ratTwo))

private theorem ratNum_zero_to_RatEq_zero {x : Rat}
    (numZero : IntEq x.num intZero) : RatEq x ratZero := by
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero := by
  apply ratNum_zero_to_RatEq_zero
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero x.num) intZero
  exact intMul_zero_left x.num

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm x ratZero) (ratMul_zero_left_local x)

private theorem ratNeg_zero_local :
    RatEq (ratNeg ratZero) ratZero := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratZero intToRat
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_zero
  · unfold ratNeg ratZero ratDenInt intToRat
    exact IntEq_refl _

private theorem ratLe_neg_anti_local {a b : Rat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local
          a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects
          (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects
        (RatEq_refl b)
        (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratLt_neg_anti_local {a b : Rat} :
    ratLt a b -> ratLt (ratNeg b) (ratNeg a) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_neg_anti_local (ratLt_to_ratLe h)
  · intro reverse
    have raw : ratLe (ratNeg (ratNeg b)) (ratNeg (ratNeg a)) :=
      ratLe_neg_anti_local reverse
    have ba : ratLe b a :=
      ratLe_respects
        (BEDC.Derived.LocatedReal.ratNeg_neg_local b)
        (BEDC.Derived.LocatedReal.ratNeg_neg_local a)
        raw
    exact ratLt_not_ratLe_reverse h ba

theorem satcycle_quadForm_eq_negFour :
    RatEq qf3 (ratNeg (natRat 4)) := by
  unfold qf3 w3 natRat
  change
    RatEq
      (ratAdd
        (ratAdd
          (ratMul ratOne (ratNeg ratTwo))
          (ratMul (ratNeg ratTwo) ratZero))
        (ratMul ratOne (ratNeg ratTwo)))
      (ratNeg ratFour)
  have first :
      RatEq (ratMul ratOne (ratNeg ratTwo)) (ratNeg ratTwo) :=
    ratOne_mul_left (ratNeg ratTwo)
  have middle :
      RatEq (ratMul (ratNeg ratTwo) ratZero) ratZero :=
    ratMul_zero_right_local (ratNeg ratTwo)
  have collapsed :
      RatEq
        (ratAdd
          (ratAdd
            (ratMul ratOne (ratNeg ratTwo))
            (ratMul (ratNeg ratTwo) ratZero))
          (ratMul ratOne (ratNeg ratTwo)))
        (ratAdd (ratNeg ratTwo) (ratNeg ratTwo)) := by
    exact RatEq_trans _ _ _
      (ratAdd_respects (ratAdd_respects first middle) first)
      (ratAdd_respects (ratAdd_zero_right (ratNeg ratTwo))
        (RatEq_refl (ratNeg ratTwo)))
  exact RatEq_trans _ _ _ collapsed
    (by
      unfold ratFour
      exact RatEq_symm
        (BEDC.Derived.LocatedReal.ratNeg_add_dist_local ratTwo ratTwo))

theorem satcycle_quadForm_neg : ratLt qf3 ratZero := by
  apply ratLt_of_RatEq_left satcycle_quadForm_eq_negFour
  change ratLt (ratNeg ratFour) ratZero
  have negStep : ratLt (ratNeg ratFour) (ratNeg ratZero) :=
    ratLt_neg_anti_local ratFour_pos
  exact ratLt_of_RatEq_right negStep ratNeg_zero_local

theorem satcycle_not_psd : ¬ ratLe ratZero qf3 := by
  intro nonnegative
  exact ratLt_not_ratLe_reverse satcycle_quadForm_neg nonnegative


/-- Bridge honest double-sum `w^T G3 w` to the reduced scalar `qf3`. -/
theorem quadForm3_G3_w3_eq_qf3 : RatEq (quadForm3 G3 w3) qf3 :=
  RatEq_refl _

/-- Genuine matrix statement: the concrete saturated-cycle Gram matrix is not PSD. -/
theorem satcycle_gram_not_psd : ¬ ratLe ratZero (quadForm3 G3 w3) := by
  intro h
  exact satcycle_not_psd (ratLe_respects (RatEq_refl ratZero) quadForm3_G3_w3_eq_qf3 h)

end BEDC.Derived.RHRoute.SaturatedCycleGramWitness
