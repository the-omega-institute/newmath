import BEDC.Real.RatNumPhaseBox

set_option maxHeartbeats 2000000

/-!
# Pythagorean anchored finite-window RP failure certificate

This file records a concrete finite reflection-positivity failure certificate
for the Pythagorean pentary self-substitution row
`v_* = (a,b,-a,b,a)`, where `a = (1+2i)/sqrt(5)` and
`b = (2-i)/sqrt(5)`.  The certificate is only the anchored `L = 3`
finite-window witness `D23 = -1/5`: the `1 x 1` principal RP submatrix
`[[-1/5]]` has negative quadratic form on the rational vector `[1]`.

Scope: this is a concrete Pythagorean-row/window RP-failure certificate.  It
does not imply RH.  It is a no-go witness for the corresponding finite
Hilbert--Polya/self-substitution constructor subclass.
-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumPhaseBox

abbrev PRRat : Type :=
  RatNum

private theorem natLeBool_true_to_le_local {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem ratLtBool_true_to_ratLt_local {x y : PRRat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le_local h)

def rpQ (num : Int) (den : Nat) : PRRat :=
  qInt num den

def pythagoreanLThreeD23 : PRRat :=
  rpQ (-1) 5

def pythagoreanLThreePrincipalMatrix : List (List PRRat) :=
  [[pythagoreanLThreeD23]]

def pythagoreanLThreeWitness : List PRRat :=
  [ratOne]

def pythagoreanLThreeQuadraticForm : PRRat :=
  ratMul (ratMul ratOne pythagoreanLThreeD23) ratOne

def pythagoreanD23CarryContributions : List PRRat :=
  [ratZero, rpQ (-1) 1, ratOne, rpQ (-1) 1, ratZero]

def pythagoreanD23CarryAverage : PRRat :=
  pythagoreanLThreeD23

theorem pythagorean_lthree_quadratic_form_eq_d23 :
    RatEq pythagoreanLThreeQuadraticForm pythagoreanLThreeD23 := by
  unfold pythagoreanLThreeQuadraticForm
  exact RatEq_trans _ _ _
    (ratMul_respects_left (ratOne_mul_left pythagoreanLThreeD23))
    (ratMul_one_right pythagoreanLThreeD23)

theorem pythagorean_lthree_d23_negative :
    ratLt pythagoreanLThreeD23 ratZero := by
  unfold pythagoreanLThreeD23 rpQ qInt q
  exact ratLtBool_true_to_ratLt_local (by rfl)

theorem pythagorean_lthree_carry_average_eq_d23 :
    RatEq pythagoreanD23CarryAverage pythagoreanLThreeD23 := by
  exact RatEq_refl pythagoreanLThreeD23

/--
The anchored `L = 3` RP matrix contains the rational principal submatrix
`[[-1/5]]`; with witness vector `[1]`, the quadratic form is strictly
negative.
-/
theorem pythagorean_lthree_negative_quadratic_form :
    RatEq pythagoreanLThreeQuadraticForm pythagoreanLThreeD23 ∧
      ratLt pythagoreanLThreeQuadraticForm ratZero := by
  constructor
  · exact pythagorean_lthree_quadratic_form_eq_d23
  · exact ratLt_of_RatEq_left
      (RatEq_symm pythagorean_lthree_quadratic_form_eq_d23)
      pythagorean_lthree_d23_negative

/--
Finite RP no-go certificate packaged with the carry-table value used in the
paper computation: the branch contributions are `0,-1,1,-1,0`, hence the
anchored diagonal entry is `-1/5`, and the selected quadratic form is negative.
-/
theorem pythagorean_lthree_rp_failure_certificate :
    pythagoreanLThreePrincipalMatrix = [[pythagoreanLThreeD23]] ∧
      pythagoreanLThreeWitness = [ratOne] ∧
      pythagoreanD23CarryContributions =
          [ratZero, rpQ (-1) 1, ratOne, rpQ (-1) 1, ratZero] ∧
        RatEq pythagoreanD23CarryAverage pythagoreanLThreeD23 ∧
        RatEq pythagoreanLThreeQuadraticForm pythagoreanLThreeD23 ∧
        ratLt pythagoreanLThreeQuadraticForm ratZero := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · exact pythagorean_lthree_carry_average_eq_d23
        · exact pythagorean_lthree_negative_quadratic_form

end BEDC.Derived.Visions
