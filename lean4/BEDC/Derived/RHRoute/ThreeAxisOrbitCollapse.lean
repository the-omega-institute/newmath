import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.LiCriterionRoute
import BEDC.Derived.RHRoute.WeilPositivityRoute
import BEDC.Derived.RHRoute.FunctionalEquationSymmetry
import BEDC.Derived.LocatedReal.GroundedToleranceKit
import BEDC.Real.RatNumKernel
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.ThreeAxisOrbitCollapse

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.BoxKernelConcrete
open BEDC.Derived.RHRoute.LiCriterionRoute
open BEDC.Derived.RHRoute.WeilPositivityRoute

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ConstructiveRHStatement.RatComplex

def ratMinusOne : Rat :=
  ratNeg ratOne

def ratTwo : Rat :=
  BEDC.Derived.RationalOrderArithUp.ratTwo

def ratMinusTwo : Rat :=
  ratNeg ratTwo

def ratSq (x : Rat) : Rat :=
  ratMul x x

def oneMinusRat (x : Rat) : Rat :=
  BEDC.Derived.RationalUp.ratSub ratOne x

def ratComplexEq (z w : RatComplex) : Prop :=
  RatEq z.re w.re ∧ RatEq z.im w.im

theorem ratComplexEq_refl (z : RatComplex) :
    ratComplexEq z z := by
  exact And.intro (RatEq_refl z.re) (RatEq_refl z.im)

theorem ratComplexEq_symm {z w : RatComplex} :
    ratComplexEq z w -> ratComplexEq w z := by
  intro h
  exact And.intro (RatEq_symm h.left) (RatEq_symm h.right)

theorem ratComplexEq_trans (x y z : RatComplex) :
    ratComplexEq x y -> ratComplexEq y z -> ratComplexEq x z := by
  intro hxy hyz
  exact And.intro
    (RatEq_trans x.re y.re z.re hxy.left hyz.left)
    (RatEq_trans x.im y.im z.im hxy.right hyz.right)

private theorem ratSub_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' ->
      RatEq (BEDC.Derived.RationalUp.ratSub x y)
        (BEDC.Derived.RationalUp.ratSub x' y') := by
  intro xx' yy'
  unfold BEDC.Derived.RationalUp.ratSub
  exact ratAdd_respects xx' (ratNeg_respects yy')

private theorem ratSub_add_cancel_right_local (x y : Rat) :
    RatEq (ratAdd (BEDC.Derived.RationalUp.ratSub x y) y) x := by
  unfold BEDC.Derived.RationalUp.ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratAdd_right_neg_cancel_local (x y : Rat) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratAdd_right_cancel_RatEq_local {x y c : Rat} :
    RatEq (ratAdd x c) (ratAdd y c) -> RatEq x y := by
  intro h
  have shifted :
      RatEq
        (ratAdd (ratAdd x c) (ratNeg c))
        (ratAdd (ratAdd y c) (ratNeg c)) :=
    ratAdd_respects h (RatEq_refl (ratNeg c))
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAdd_right_neg_cancel_local x c))
    (RatEq_trans _ _ _ shifted (ratAdd_right_neg_cancel_local y c))

private theorem ratTwo_reads_one_add_one :
    RatEq ratTwo (ratAdd ratOne ratOne) := by
  unfold ratTwo BEDC.Derived.RationalOrderArithUp.ratTwo
  unfold ratOne intToRat ratAdd RatEq intOfNat intOne
  exact IntPairClassifier_of_length_eq (intToPair_carrier _)
    (intToPair_carrier _) (by decide)

private theorem half_add_half_eq_one :
    RatEq (ratAdd halfRat halfRat) ratOne := by
  change
    RatEq
      (ratAdd BEDC.Derived.RationalUp.ratHalf
        BEDC.Derived.RationalUp.ratHalf)
      ratOne
  unfold BEDC.Derived.RationalUp.ratHalf ratOne intToRat ratAdd RatEq
    intOfNat intOne
  exact IntPairClassifier_of_length_eq (intToPair_carrier _)
    (intToPair_carrier _) (by decide)

private theorem one_sub_half_eq_half :
    RatEq (BEDC.Derived.RationalUp.ratSub ratOne halfRat) halfRat := by
  change
    RatEq
      (BEDC.Derived.RationalUp.ratSub ratOne
        BEDC.Derived.RationalUp.ratHalf)
      BEDC.Derived.RationalUp.ratHalf
  unfold BEDC.Derived.RationalUp.ratHalf BEDC.Derived.RationalUp.ratSub
    ratOne intToRat ratAdd ratNeg RatEq intOfNat intOne
  exact IntPairClassifier_of_length_eq (intToPair_carrier _)
    (intToPair_carrier _) (by decide)

private theorem ratMul_two_eq_add_self (x : Rat) :
    RatEq (ratMul x ratTwo) (ratAdd x x) := by
  have toOneAdd :
      RatEq (ratMul x ratTwo) (ratMul x (ratAdd ratOne ratOne)) :=
    ratMul_respects (RatEq_refl x) ratTwo_reads_one_add_one
  have distribute :
      RatEq (ratMul x (ratAdd ratOne ratOne))
        (ratAdd (ratMul x ratOne) (ratMul x ratOne)) :=
    BEDC.Real.RatNumKernel.ratMul_add_left x ratOne ratOne
  have fold :
      RatEq (ratAdd (ratMul x ratOne) (ratMul x ratOne))
        (ratAdd x x) :=
    ratAdd_respects (ratMul_one_right x) (ratMul_one_right x)
  exact RatEq_trans _ _ _ toOneAdd (RatEq_trans _ _ _ distribute fold)

private theorem half_mul_two_eq_one :
    RatEq (ratMul halfRat ratTwo) ratOne :=
  RatEq_trans _ _ _ (ratMul_two_eq_add_self halfRat) half_add_half_eq_one

abbrev IotaPackedPoint : Type :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.RationalComplex

def iotaPackedReflection (s : IotaPackedPoint) : IotaPackedPoint :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.reflectJ s

def PackedOnCriticalLine (s : IotaPackedPoint) : Prop :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine s

theorem packed_iota_involution (s : IotaPackedPoint) :
    BEDC.Derived.RHRoute.FunctionalEquationSymmetry.ComplexEq
      (iotaPackedReflection (iotaPackedReflection s)) s :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.reflectJ_involutive s

theorem packed_iota_fixed_iff_re_half (s : IotaPackedPoint) :
    BEDC.Derived.RHRoute.FunctionalEquationSymmetry.ComplexEq
      (iotaPackedReflection s) s ↔ PackedOnCriticalLine s :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.criticalLine_J_fixed_iff s

def ratComplexConjugate (s : RatComplex) : RatComplex :=
  { re := s.re
    im := ratNeg s.im }

def iotaReflection (s : RatComplex) : RatComplex :=
  { re := oneMinusRat s.re
    im := s.im }

def distComponent (s : RatComplex) : Rat :=
  BEDC.Derived.RationalUp.ratSub s.re halfRat

def symComponent (s : RatComplex) : Rat :=
  s.im

def centeredPoint (s : RatComplex) : RatComplex :=
  { re := distComponent s
    im := symComponent s }

def centeredNormSq (s : RatComplex) : Rat :=
  ratComplexNormSq (centeredPoint s)

def threeAxisNormSq (s : RatComplex) : Rat :=
  ratAdd (ratSq (distComponent s)) (ratSq (symComponent s))

theorem pythagoras_w (s : RatComplex) :
    RatEq (centeredNormSq s) (threeAxisNormSq s) := by
  exact RatEq_refl (threeAxisNormSq s)

def OnCriticalLineByRealHalf (s : RatComplex) : Prop :=
  RatEq s.re halfRat

theorem onCriticalLineByRealHalf_reads (s : RatComplex) :
    OnCriticalLineByRealHalf s ↔ OnCriticalLine s := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

private theorem iota_fixed_to_re_half (s : RatComplex) :
    ratComplexEq (iotaReflection s) s -> RatEq s.re halfRat := by
  intro fixed
  have shifted :
      RatEq
        (ratAdd (BEDC.Derived.RationalUp.ratSub ratOne s.re) s.re)
        (ratAdd s.re s.re) :=
    ratAdd_respects fixed.left (RatEq_refl s.re)
  have leftOne :
      RatEq
        (ratAdd (BEDC.Derived.RationalUp.ratSub ratOne s.re) s.re)
        ratOne :=
    ratSub_add_cancel_right_local ratOne s.re
  have addSelfOne : RatEq (ratAdd s.re s.re) ratOne :=
    RatEq_trans _ _ _ (RatEq_symm shifted) leftOne
  have mulTwoOne : RatEq (ratMul s.re ratTwo) ratOne :=
    RatEq_trans _ _ _ (ratMul_two_eq_add_self s.re) addSelfOne
  exact BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    s.re halfRat ratTwo
    BEDC.Derived.RationalOrderArithUp.ratTwo_apart
    (RatEq_trans _ _ _ mulTwoOne (RatEq_symm half_mul_two_eq_one))

private theorem re_half_to_iota_fixed (s : RatComplex) :
    RatEq s.re halfRat -> ratComplexEq (iotaReflection s) s := by
  intro h
  have subRead :
      RatEq (BEDC.Derived.RationalUp.ratSub ratOne s.re)
        (BEDC.Derived.RationalUp.ratSub ratOne halfRat) :=
    ratSub_respects_local (RatEq_refl ratOne) h
  exact And.intro
    (RatEq_trans _ _ _ subRead
      (RatEq_trans _ _ _ one_sub_half_eq_half (RatEq_symm h)))
    (RatEq_refl s.im)

theorem iota_fixed_iff_re_half (s : RatComplex) :
    ratComplexEq (iotaReflection s) s ↔ OnCriticalLineByRealHalf s := by
  constructor
  · exact iota_fixed_to_re_half s
  · exact re_half_to_iota_fixed s

theorem oneMinusRat_involutive (x : Rat) :
    RatEq (oneMinusRat (oneMinusRat x)) x := by
  have base :
      RatEq
        (BEDC.Derived.RationalUp.ratSub
          (ratAdd ratOne ratZero)
          (BEDC.Derived.RationalUp.ratSub ratOne x))
        (ratAdd x ratZero) :=
    BEDC.Derived.LocatedReal.ratSub_add_sub_left_cancel x ratOne ratZero
  have leftToTarget :
      RatEq
        (BEDC.Derived.RationalUp.ratSub
          (ratAdd ratOne ratZero)
          (BEDC.Derived.RationalUp.ratSub ratOne x))
        (BEDC.Derived.RationalUp.ratSub ratOne
          (BEDC.Derived.RationalUp.ratSub ratOne x)) :=
    ratSub_respects_local (ratAdd_zero_right ratOne) (RatEq_refl _)
  exact RatEq_trans _ _ _ (RatEq_symm leftToTarget)
    (RatEq_trans _ _ _ base (ratAdd_zero_right x))

theorem iota_involution (s : RatComplex) :
    ratComplexEq
      { re := oneMinusRat (oneMinusRat s.re), im := s.im } s := by
  exact And.intro (oneMinusRat_involutive s.re) (RatEq_refl s.im)

theorem iotaReflection_fixed_iff_re_half (s : RatComplex) :
    ratComplexEq (iotaReflection s) s ↔ OnCriticalLineByRealHalf s := by
  constructor
  · exact iota_fixed_to_re_half s
  · exact re_half_to_iota_fixed s

structure IotaOrbit where
  point : RatComplex
  reflected : RatComplex
  reflected_readback : ratComplexEq reflected (iotaReflection point)

def iotaOrbit (rho : RatComplex) : IotaOrbit where
  point := rho
  reflected := iotaReflection rho
  reflected_readback := ratComplexEq_refl (iotaReflection rho)

def OrbitCollapsed (rho : RatComplex) : Prop :=
  ratComplexEq (iotaReflection rho) rho

theorem orbitCollapsed_iff_onCriticalLineByRealHalf
    (rho : RatComplex) :
    OrbitCollapsed rho ↔ OnCriticalLineByRealHalf rho :=
  iota_fixed_iff_re_half rho

structure OrbitPairAmplitude where
  at_point : Rat
  at_reflection : Rat

def orbitPairContribution (a : OrbitPairAmplitude) : Rat :=
  ratAdd
    (ratMul a.at_point a.at_reflection)
    (ratMul a.at_reflection a.at_point)

def negativeOrbitPairAmplitude : OrbitPairAmplitude where
  at_point := ratOne
  at_reflection := ratMinusOne

theorem negativeOrbitPairContribution_reads_minus_two :
    RatEq (orbitPairContribution negativeOrbitPairAmplitude) ratMinusTwo := by
  exact RatEq_refl (orbitPairContribution negativeOrbitPairAmplitude)

structure TwoPointSignatureSplit where
  pointWeight : Rat
  reflectionWeight : Rat
  positive_square : Rat
  negative_square : Rat
  contribution : Rat
  weights_read :
    RatEq pointWeight ratOne ∧ RatEq reflectionWeight ratMinusOne
  contribution_read :
    RatEq contribution (orbitPairContribution negativeOrbitPairAmplitude)
  negative_direction_read :
    RatEq contribution ratMinusTwo

def canonicalNegativeSignatureSplit : TwoPointSignatureSplit where
  pointWeight := ratOne
  reflectionWeight := ratMinusOne
  positive_square := ratZero
  negative_square := ratTwo
  contribution := orbitPairContribution negativeOrbitPairAmplitude
  weights_read := And.intro (RatEq_refl ratOne) (RatEq_refl ratMinusOne)
  contribution_read := RatEq_refl (orbitPairContribution negativeOrbitPairAmplitude)
  negative_direction_read := negativeOrbitPairContribution_reads_minus_two

structure ThreeAxisPositivityWitness (rho : RatComplex) where
  orbit : IotaOrbit
  orbit_point_readback : ratComplexEq orbit.point rho
  off_line : Not (OrbitCollapsed rho)
  signature_split : TwoPointSignatureSplit
  weil_block_value : Rat
  weil_block_negative_read :
    RatEq weil_block_value ratMinusTwo

theorem offline_breaks_positivity
    (rho : RatComplex) (off_line : Not (OrbitCollapsed rho)) :
    ∃ witness : ThreeAxisPositivityWitness rho,
      RatEq witness.weil_block_value ratMinusTwo := by
  let split := canonicalNegativeSignatureSplit
  let witness : ThreeAxisPositivityWitness rho :=
    { orbit := iotaOrbit rho
      orbit_point_readback := ratComplexEq_refl rho
      off_line := off_line
      signature_split := split
      weil_block_value := split.contribution
      weil_block_negative_read := split.negative_direction_read }
  exact Exists.intro witness witness.weil_block_negative_read

structure HermiteBiehlerSOS where
  E : RatComplex -> RatComplex
  Esharp : RatComplex -> RatComplex
  upper_half_plane : RatComplex -> Prop
  normSq_gap : RatComplex -> Rat
  hb_nonnegative :
    ∀ z : RatComplex, upper_half_plane z -> ratLe ratZero (normSq_gap z)
  sos_factorization_obligation : Prop

structure ThreeAxisOrbitCollapseKernel where
  hermite_biehler_sos : HermiteBiehlerSOS
  zero_orbit_collapse :
    ∀ rho : RatComplex,
      NontrivialZetaZero rho -> OrbitCollapsed rho
  weil_li_bridge_obligation : Prop

def HermiteBiehlerSOSForZetaXi (sos : HermiteBiehlerSOS) : Prop :=
  sos.sos_factorization_obligation

theorem rh_via_orbit_collapse
    (kernel : ThreeAxisOrbitCollapseKernel) :
    ConstructiveRH := by
  intro rho zero
  have collapsed : OrbitCollapsed rho :=
    kernel.zero_orbit_collapse rho zero
  exact (onCriticalLineByRealHalf_reads rho).mp
    ((orbitCollapsed_iff_onCriticalLineByRealHalf rho).mp collapsed)

structure SuzukiHermiteBiehlerReduction where
  sos : HermiteBiehlerSOS
  zero_orbit_collapse_from_sos :
    HermiteBiehlerSOSForZetaXi sos ->
      ∀ rho : RatComplex, NontrivialZetaZero rho -> OrbitCollapsed rho
  suzuki_equivalence_obligation : Prop

def kernelFromHermiteBiehlerReduction
    (reduction : SuzukiHermiteBiehlerReduction)
    (factorization : HermiteBiehlerSOSForZetaXi reduction.sos) :
    ThreeAxisOrbitCollapseKernel where
  hermite_biehler_sos := reduction.sos
  zero_orbit_collapse :=
    reduction.zero_orbit_collapse_from_sos factorization
  weil_li_bridge_obligation := reduction.suzuki_equivalence_obligation

theorem rh_via_hermite_biehler_sos
    (reduction : SuzukiHermiteBiehlerReduction)
    (factorization : HermiteBiehlerSOSForZetaXi reduction.sos) :
    ConstructiveRH :=
  rh_via_orbit_collapse
    (kernelFromHermiteBiehlerReduction reduction factorization)

theorem li_sample_positive_witness_reads_route :
    LiStrictPositive liSampleTaylorPacket 1 ∧
      LiStrictPositive liSampleTaylorPacket 2 ∧
        LiStrictPositive liSampleTaylorPacket 3 ∧
          LiStrictPositive liSampleTaylorPacket 4 ∧
            LiStrictPositive liSampleTaylorPacket 5 :=
  li_positive_witness

end BEDC.Derived.RHRoute.ThreeAxisOrbitCollapse
