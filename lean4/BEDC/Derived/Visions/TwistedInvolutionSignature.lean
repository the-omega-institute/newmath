import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# Twisted involution signature in a concrete RatNum plane

This file records the 2D schematic algebra behind the iota-twist bridge.  The
Euclidean Gram form supplies the positive basis, while the reflection `iota`
twists the second coordinate.  The negative self-pairing is derived from the
`-1` eigendirection: `gIota v v = G v (iota v) = G v (-v) = -G v v`.

Scope: this is a concrete `RatNum` model, not a physical metric theorem.  The
general-dimensional signature theorem and the bridge to the BEDC reflection
apparatus remain further work.
-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.LocatedReal (ratNeg_neg_local)

abbrev Vec2 : Type :=
  RatNum × RatNum

/-- Standard positive Gram form on the concrete `RatNum` plane. -/
def G (u v : Vec2) : RatNum :=
  ratAdd (ratMul u.1 v.1) (ratMul u.2 v.2)

/-- Reflection of the second coordinate. -/
def iota (v : Vec2) : Vec2 :=
  (v.1, ratNeg v.2)

/-- The twisted form `g_iota(u,v) = G(u, iota v)`. -/
def gIota (u v : Vec2) : RatNum :=
  G u (iota v)

/-- Componentwise rational equality for vectors. -/
def VecEq (u v : Vec2) : Prop :=
  RatEq u.1 v.1 ∧ RatEq u.2 v.2

private theorem ratNum_zero_to_RatEq_zero {x : RatNum} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
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

private theorem ratMul_zero_left (x : RatNum) :
    RatEq (ratMul ratZero x) ratZero := by
  apply ratNum_zero_to_RatEq_zero
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero x.num) intZero
  exact intMul_zero_left x.num

private theorem ratMul_zero_right (x : RatNum) :
    RatEq (ratMul x ratZero) ratZero := by
  exact RatEq_trans _ _ _
    (ratMul_comm x ratZero)
    (ratMul_zero_left x)

/-- Multiplying by a negative factor moves the sign to the product. -/
private theorem ratMul_neg_right (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratMul_neg_left (x y : RatNum) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratNeg x) y)
    (RatEq_trans _ _ _
      (ratMul_neg_right y x)
      (ratNeg_respects (ratMul_comm y x)))

private theorem ratMul_neg_neg (x y : RatNum) :
    RatEq (ratMul (ratNeg x) (ratNeg y)) (ratMul x y) := by
  exact RatEq_trans _ _ _
    (ratMul_neg_left x (ratNeg y))
    (RatEq_trans _ _ _
      (ratNeg_respects (ratMul_neg_right x y))
      (ratNeg_neg_local (ratMul x y)))

private theorem ratNeg_nonneg_of_nonpos {x : RatNum} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro hx
  have raw :
      ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le (x := ratZero) (y := x) hx
  unfold ratSub at raw
  exact ratLe_respects (RatEq_refl ratZero) (ratZero_add_left (ratNeg x)) raw

/-- Explicit constructive square nonnegativity for `RatNum`, without automation. -/
private theorem ratMul_self_nonneg (x : RatNum) :
    ratLe ratZero (ratMul x x) := by
  cases ratLe_total ratZero x with
  | inl xNonneg =>
      exact ratMul_nonneg xNonneg xNonneg
  | inr xNonpos =>
      have negNonneg : ratLe ratZero (ratNeg x) :=
        ratNeg_nonneg_of_nonpos xNonpos
      have negSquareNonneg :
          ratLe ratZero (ratMul (ratNeg x) (ratNeg x)) :=
        ratMul_nonneg negNonneg negNonneg
      exact ratLe_respects
        (RatEq_refl ratZero)
        (ratMul_neg_neg x x)
        negSquareNonneg

theorem iota_involution (v : Vec2) :
    VecEq (iota (iota v)) v := by
  cases v with
  | mk x y =>
      constructor
      · exact RatEq_refl x
      · change RatEq (ratNeg (ratNeg y)) y
        exact ratNeg_neg_local y

/-- The twisted form is symmetric: the reflection sign is carried by algebra. -/
theorem gIota_symm (u v : Vec2) :
    RatEq (gIota u v) (gIota v u) := by
  cases u with
  | mk ux uy =>
      cases v with
      | mk vx vy =>
          change
            RatEq
              (ratAdd (ratMul ux vx) (ratMul uy (ratNeg vy)))
              (ratAdd (ratMul vx ux) (ratMul vy (ratNeg uy)))
          have first :
              RatEq (ratMul ux vx) (ratMul vx ux) :=
            ratMul_comm ux vx
          have second :
              RatEq (ratMul uy (ratNeg vy)) (ratMul vy (ratNeg uy)) :=
            RatEq_trans _ _ _
              (ratMul_neg_right uy vy)
              (RatEq_trans _ _ _
                (ratNeg_respects (ratMul_comm uy vy))
                (RatEq_symm (ratMul_neg_right vy uy)))
          exact ratAdd_respects first second

private theorem G_plus_axis_value (x : RatNum) :
    RatEq (G (x, ratZero) (x, ratZero)) (ratMul x x) := by
  change
    RatEq
      (ratAdd (ratMul x x) (ratMul ratZero ratZero))
      (ratMul x x)
  exact RatEq_trans _ _ _
    (ratAdd_respects
      (RatEq_refl (ratMul x x))
      (ratMul_zero_left ratZero))
    (ratAdd_zero_right (ratMul x x))

private theorem gIota_plus_axis_value (x : RatNum) :
    RatEq (gIota (x, ratZero) (x, ratZero)) (ratMul x x) := by
  change
    RatEq
      (ratAdd (ratMul x x) (ratMul ratZero (ratNeg ratZero)))
      (ratMul x x)
  exact RatEq_trans _ _ _
    (ratAdd_respects
      (RatEq_refl (ratMul x x))
      (ratMul_zero_left (ratNeg ratZero)))
    (ratAdd_zero_right (ratMul x x))

private theorem G_minus_axis_value (y : RatNum) :
    RatEq (G (ratZero, y) (ratZero, y)) (ratMul y y) := by
  change
    RatEq
      (ratAdd (ratMul ratZero ratZero) (ratMul y y))
      (ratMul y y)
  exact RatEq_trans _ _ _
    (ratAdd_respects
      (ratMul_zero_left ratZero)
      (RatEq_refl (ratMul y y)))
    (ratZero_add_left (ratMul y y))

private theorem gIota_minus_axis_value (y : RatNum) :
    RatEq (gIota (ratZero, y) (ratZero, y)) (ratNeg (ratMul y y)) := by
  change
    RatEq
      (ratAdd (ratMul ratZero ratZero) (ratMul y (ratNeg y)))
      (ratNeg (ratMul y y))
  exact RatEq_trans _ _ _
    (ratAdd_respects
      (ratMul_zero_left ratZero)
      (RatEq_refl (ratMul y (ratNeg y))))
    (RatEq_trans _ _ _
      (ratZero_add_left (ratMul y (ratNeg y)))
      (ratMul_neg_right y y))

/--
On the `-1` axis, the negative sign is derived by the twist:
`gIota (0,y) (0,y) = G (0,y) (0,-y) = -(y*y)`.  The nonpositive
conclusion uses square nonnegativity of the Euclidean Gram value.
-/
theorem twisted_neg_eigen_self_pairing_neg (y : RatNum) :
    RatEq (gIota (ratZero, y) (ratZero, y))
        (ratNeg (G (ratZero, y) (ratZero, y))) ∧
      RatEq (G (ratZero, y) (ratZero, y)) (ratMul y y) ∧
      RatEq (gIota (ratZero, y) (ratZero, y)) (ratNeg (ratMul y y)) ∧
      ratLe (gIota (ratZero, y) (ratZero, y)) ratZero := by
  have gValue :
      RatEq (gIota (ratZero, y) (ratZero, y)) (ratNeg (ratMul y y)) :=
    gIota_minus_axis_value y
  have GValue :
      RatEq (G (ratZero, y) (ratZero, y)) (ratMul y y) :=
    G_minus_axis_value y
  have gAsNegG :
      RatEq (gIota (ratZero, y) (ratZero, y))
        (ratNeg (G (ratZero, y) (ratZero, y))) :=
    RatEq_trans _ _ _
      gValue
      (RatEq_symm (ratNeg_respects GValue))
  have squareNonneg :
      ratLe ratZero (ratMul y y) :=
    ratMul_self_nonneg y
  have negSquareLeZero :
      ratLe (ratNeg (ratMul y y)) ratZero := by
    have raw :
        ratLe (ratSub ratZero (ratMul y y)) ratZero :=
      ratSub_le_left_of_nonneg (x := ratZero) (y := ratMul y y) squareNonneg
    unfold ratSub at raw
    exact ratLe_respects
      (ratZero_add_left (ratNeg (ratMul y y)))
      (RatEq_refl ratZero)
      raw
  have gLeZero :
      ratLe (gIota (ratZero, y) (ratZero, y)) ratZero :=
    ratLe_respects
      (RatEq_symm gValue)
      (RatEq_refl ratZero)
      negSquareLeZero
  exact ⟨gAsNegG, GValue, gValue, gLeZero⟩

/--
On the `+1` axis, the twist leaves the Euclidean square unchanged:
`gIota (x,0) (x,0) = x*x`, hence the self-pairing is nonnegative.
-/
theorem twisted_plus_eigen_self_pairing_nonneg (x : RatNum) :
    RatEq (gIota (x, ratZero) (x, ratZero)) (ratMul x x) ∧
      RatEq (G (x, ratZero) (x, ratZero)) (ratMul x x) ∧
      ratLe ratZero (gIota (x, ratZero) (x, ratZero)) := by
  have gValue :
      RatEq (gIota (x, ratZero) (x, ratZero)) (ratMul x x) :=
    gIota_plus_axis_value x
  have GValue :
      RatEq (G (x, ratZero) (x, ratZero)) (ratMul x x) :=
    G_plus_axis_value x
  have squareNonneg :
      ratLe ratZero (ratMul x x) :=
    ratMul_self_nonneg x
  have gNonneg :
      ratLe ratZero (gIota (x, ratZero) (x, ratZero)) :=
    ratLe_respects
      (RatEq_refl ratZero)
      (RatEq_symm gValue)
      squareNonneg
  exact ⟨gValue, GValue, gNonneg⟩

end BEDC.Derived.Visions
