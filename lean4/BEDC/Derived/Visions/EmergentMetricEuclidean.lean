import BEDC.Derived.Visions.TwoDriverMetricNondegeneracy

set_option maxHeartbeats 2000000

/-!
# Emergent metric determinant sign

The two-driver observation backreaction matrix formalized in
`TwoDriverMetricNondegeneracy` is a weighted Gram matrix:

$$
g = w_1\,\Delta_1 \otimes \Delta_1 + w_2\,\Delta_2 \otimes \Delta_2.
$$

With nonnegative weights its determinant is

$$
w_1 w_2 (\Delta_1 \wedge \Delta_2)^2,
$$

hence nonnegative. This is a determinant-sign obstruction to a Lorentzian
two-dimensional metric, where one negative eigenvalue forces determinant
`< 0`. A Lorentzian branch would need an explicit timelike driver, namely a
negative self-pairing term; that is not derived by this schematic carrier.

The content here is algebraic and schematic. It records the falsifiable
boundary: observation-driven rank-one positive self-pairings yield the
Euclidean Gram determinant sign, not a Lorentzian signature.
-/

namespace BEDC.Derived.Visions

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

/-- A rational square is nonnegative. The proof works at the numerator:
`x*x` has numerator equal to the natural product of the numerator magnitude
with itself, so it is an integer-from-Nat and therefore `>= 0`. -/
private theorem ratMul_self_nonneg_local (x : RatNum) :
    ratLe ratZero (ratMul x x) := by
  apply ratNonneg_of_num
  have squareNum :
      IntEq (ratMul x x).num
        (intOfNat (natMulFn x.num.magnitude x.num.magnitude)
          (natMulFn_unary x.num.carrier.right x.num.carrier.right)) := by
    change IntEq (IntMul x.num x.num)
      (intOfNat (natMulFn x.num.magnitude x.num.magnitude)
        (natMulFn_unary x.num.carrier.right x.num.carrier.right))
    exact intMul_same_sign_nat x.num.sign x.num.magnitude x.num.magnitude
      x.num.carrier.right x.num.carrier.right
  exact intLe_respects (IntEq_refl intZero) (IntEq_symm squareNum)
    (intLe_zero_of_nat (natMulFn x.num.magnitude x.num.magnitude)
      (natMulFn_unary x.num.carrier.right x.num.carrier.right))

/-- Nonnegative two-driver weights force the determinant of the emergent
backreaction Gram matrix to be nonnegative. -/
theorem two_driver_det_nonneg (w1 w2 a1 a2 b1 b2 : RatNum)
    (hw1 : ratLe ratZero w1) (hw2 : ratLe ratZero w2) :
    ratLe ratZero (twoDriverMetricDet w1 w2 a1 a2 b1 b2) := by
  let delta := wedge a1 a2 b1 b2
  have weightsNonneg : ratLe ratZero (ratMul w1 w2) :=
    ratMul_nonneg hw1 hw2
  have squareNonneg : ratLe ratZero (ratMul delta delta) :=
    ratMul_self_nonneg_local delta
  have productNonneg :
      ratLe ratZero (ratMul (ratMul w1 w2) (ratMul delta delta)) :=
    ratMul_nonneg weightsNonneg squareNonneg
  have regroup :
      RatEq (ratMul (ratMul (ratMul w1 w2) delta) delta)
        (ratMul (ratMul w1 w2) (ratMul delta delta)) :=
    ratMul_assoc (ratMul w1 w2) delta delta
  have detEq :
      RatEq (twoDriverMetricDet w1 w2 a1 a2 b1 b2)
        (ratMul (ratMul w1 w2) (ratMul delta delta)) :=
    RatEq_trans _ _ _
      (two_driver_det_eq_weighted_wedge_sq w1 w2 a1 a2 b1 b2)
      regroup
  exact ratLe_of_RatEq_right productNonneg (RatEq_symm detEq)

/-- A negative determinant request is incompatible with the nonnegative
two-driver Gram construction. This is the formal Lorentzian-sign exclusion
for the schematic carrier. -/
theorem lorentzian_signature_excluded (w1 w2 a1 a2 b1 b2 : RatNum)
    (hw1 : ratLe ratZero w1) (hw2 : ratLe ratZero w2) :
    ratLt (twoDriverMetricDet w1 w2 a1 a2 b1 b2) ratZero -> False := by
  intro detNeg
  exact ratLt_not_ratLe_reverse detNeg
    (two_driver_det_nonneg w1 w2 a1 a2 b1 b2 hw1 hw2)

end BEDC.Derived.Visions
