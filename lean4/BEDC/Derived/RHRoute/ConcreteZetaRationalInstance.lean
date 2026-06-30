import BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace BEDC.Derived.RHRoute.ConcreteZetaRationalInstance

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.KrawczykCertificate

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev ZetaAnalyticInterface : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ZetaAnalyticInterface

abbrev CFun : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.CFun

abbrev CMap : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.CMap

abbrev CBox : Type :=
  BEDC.ZetaCert.CBox

abbrev DyI : Type :=
  BEDC.ZetaCert.Dy.I

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

def exactSingletonBox (z : RatComplex) : ComplexBox :=
  { re := { lo := z.re, hi := z.re, valid := ratLe_refl z.re }
    im := { lo := z.im, hi := z.im, valid := ratLe_refl z.im } }

def ratOfIntOverNat (num : Int) (den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat num den

def dyMantissaToRat (m : Int) : Rat :=
  ratOfIntOverNat m BEDC.ZetaCert.Dy.S.natAbs

def dyIntervalCenterMantissa (I : DyI) : Int :=
  (I.lo + I.hi) / 2

def dyIntervalCenterRat (I : DyI) : Rat :=
  dyMantissaToRat (dyIntervalCenterMantissa I)

def cboxCenterRatComplex (box : CBox) : RatComplex :=
  { re := dyIntervalCenterRat box.re
    im := dyIntervalCenterRat box.im }

def powApprox24 (m : Nat) : RatComplex :=
  cboxCenterRatComplex
    ((BEDC.ZetaCert.PowBoxes.powBoxes.getD (m - 1)
      BEDC.ZetaCert.PowBoxes.defaultPowBox).box)

def lnApprox24 (m : Nat) : RatComplex :=
  { re := dyIntervalCenterRat
      ((BEDC.ZetaCert.PowBoxes.powBoxes.getD (m - 1)
        BEDC.ZetaCert.PowBoxes.defaultPowBox).ln)
    im := ratZero }

def coeffApprox24 (i : Nat) : Rat :=
  dyIntervalCenterRat (BEDC.ZetaCert.Hasse24.coeff24N i)

def concreteZeta24Value : RatComplex :=
  BEDC.Derived.RHRoute.EulerHasseRegroup.etaGrouped 24
    (fun m => powApprox24 m)

def concreteZeta24DerivativeValue : RatComplex :=
  BEDC.Derived.RHRoute.EulerHasseRegroup.sumComplex 24
    (fun j =>
      let m := Nat.succ j
      let term := BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexMul
        (lnApprox24 m) (powApprox24 m)
      BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexScale
        (ratNeg (BEDC.Derived.RHRoute.EulerHasseRegroup.etaCoeff 24 m))
        term)

-- `concreteZeta24` is a concrete M=24 rational Euler-Hasse approximation
-- with fixed dyadic centers. It is not the classical zeta function.
def concreteZeta24 : ZetaAnalyticInterface :=
  { zeta := { evalRat := fun _z => concreteZeta24Value }
    zetaDerivative := { evalRat := fun _z => concreteZeta24DerivativeValue } }

theorem concreteZeta24_zeta_readback (z : RatComplex) :
    concreteZeta24.zeta z = concreteZeta24Value := by
  rfl

theorem concreteZeta24_derivative_readback (z : RatComplex) :
    concreteZeta24.zetaDerivative z = concreteZeta24DerivativeValue := by
  rfl

theorem zetaFormal_concreteZeta24_mem_exact_value_box (z : RatComplex) :
    ComplexInBox
      (BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.zetaFormal
        concreteZeta24 z)
      (exactSingletonBox concreteZeta24Value) := by
  exact ⟨⟨ratLe_refl concreteZeta24Value.re,
    ratLe_refl concreteZeta24Value.re⟩,
    ⟨ratLe_refl concreteZeta24Value.im,
      ratLe_refl concreteZeta24Value.im⟩⟩

theorem concreteZeta24_kernel_depth :
    BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.zeta14BoolKernelDepth = 24 := by
  exact
    BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.zeta14BoolKernelDepth_readback

theorem concreteZeta24_pow_table_size :
    BEDC.ZetaCert.PowBoxes.powBoxes.size = 24 := by
  exact BEDC.ZetaCert.PowBoxes.powBoxes_size

theorem concreteZeta24_coeff_table_size :
    BEDC.ZetaCert.Hasse24.coeffNum24.size = 24 := by
  exact BEDC.ZetaCert.Hasse24.coeffNum24_size

theorem concreteZeta24_coeff_table_is_hasse24 :
    BEDC.ZetaCert.Hasse24.coeffNum24List =
      BEDC.ZetaCert.Hasse24.coeffNum24GenList := by
  exact BEDC.ZetaCert.Hasse24.coeffNum24_eq_gen_list

def DyMemI (m : Int) (I : DyI) : Prop :=
  BEDC.ZetaCert.Dy.MemM m I

def CBoxCenterMantissaMem (box : CBox) : Prop :=
  DyMemI (dyIntervalCenterMantissa box.re) box.re ∧
    DyMemI (dyIntervalCenterMantissa box.im) box.im

def powBoxCenterMantissaMemAt (i : Nat) : Prop :=
  CBoxCenterMantissaMem
    ((BEDC.ZetaCert.PowBoxes.powBoxes.getD i
      BEDC.ZetaCert.PowBoxes.defaultPowBox).box)

theorem powApprox24_mem_powBox_1 :
    powBoxCenterMantissaMemAt 0 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_2 :
    powBoxCenterMantissaMemAt 1 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_3 :
    powBoxCenterMantissaMemAt 2 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_4 :
    powBoxCenterMantissaMemAt 3 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_5 :
    powBoxCenterMantissaMemAt 4 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_6 :
    powBoxCenterMantissaMemAt 5 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_7 :
    powBoxCenterMantissaMemAt 6 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_8 :
    powBoxCenterMantissaMemAt 7 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_9 :
    powBoxCenterMantissaMemAt 8 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_10 :
    powBoxCenterMantissaMemAt 9 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_11 :
    powBoxCenterMantissaMemAt 10 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_12 :
    powBoxCenterMantissaMemAt 11 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_13 :
    powBoxCenterMantissaMemAt 12 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_14 :
    powBoxCenterMantissaMemAt 13 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_15 :
    powBoxCenterMantissaMemAt 14 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_16 :
    powBoxCenterMantissaMemAt 15 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_17 :
    powBoxCenterMantissaMemAt 16 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_18 :
    powBoxCenterMantissaMemAt 17 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_19 :
    powBoxCenterMantissaMemAt 18 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_20 :
    powBoxCenterMantissaMemAt 19 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_21 :
    powBoxCenterMantissaMemAt 20 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_22 :
    powBoxCenterMantissaMemAt 21 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_23 :
    powBoxCenterMantissaMemAt 22 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_mem_powBox_24 :
    powBoxCenterMantissaMemAt 23 := by
  unfold powBoxCenterMantissaMemAt CBoxCenterMantissaMem DyMemI
    BEDC.ZetaCert.Dy.MemM dyIntervalCenterMantissa
  decide

theorem powApprox24_all_centers_mem_powBoxes :
    powBoxCenterMantissaMemAt 0 ∧
      powBoxCenterMantissaMemAt 1 ∧
      powBoxCenterMantissaMemAt 2 ∧
      powBoxCenterMantissaMemAt 3 ∧
      powBoxCenterMantissaMemAt 4 ∧
      powBoxCenterMantissaMemAt 5 ∧
      powBoxCenterMantissaMemAt 6 ∧
      powBoxCenterMantissaMemAt 7 ∧
      powBoxCenterMantissaMemAt 8 ∧
      powBoxCenterMantissaMemAt 9 ∧
      powBoxCenterMantissaMemAt 10 ∧
      powBoxCenterMantissaMemAt 11 ∧
      powBoxCenterMantissaMemAt 12 ∧
      powBoxCenterMantissaMemAt 13 ∧
      powBoxCenterMantissaMemAt 14 ∧
      powBoxCenterMantissaMemAt 15 ∧
      powBoxCenterMantissaMemAt 16 ∧
      powBoxCenterMantissaMemAt 17 ∧
      powBoxCenterMantissaMemAt 18 ∧
      powBoxCenterMantissaMemAt 19 ∧
      powBoxCenterMantissaMemAt 20 ∧
      powBoxCenterMantissaMemAt 21 ∧
      powBoxCenterMantissaMemAt 22 ∧
      powBoxCenterMantissaMemAt 23 := by
  exact
    ⟨powApprox24_mem_powBox_1,
      powApprox24_mem_powBox_2,
      powApprox24_mem_powBox_3,
      powApprox24_mem_powBox_4,
      powApprox24_mem_powBox_5,
      powApprox24_mem_powBox_6,
      powApprox24_mem_powBox_7,
      powApprox24_mem_powBox_8,
      powApprox24_mem_powBox_9,
      powApprox24_mem_powBox_10,
      powApprox24_mem_powBox_11,
      powApprox24_mem_powBox_12,
      powApprox24_mem_powBox_13,
      powApprox24_mem_powBox_14,
      powApprox24_mem_powBox_15,
      powApprox24_mem_powBox_16,
      powApprox24_mem_powBox_17,
      powApprox24_mem_powBox_18,
      powApprox24_mem_powBox_19,
      powApprox24_mem_powBox_20,
      powApprox24_mem_powBox_21,
      powApprox24_mem_powBox_22,
      powApprox24_mem_powBox_23,
      powApprox24_mem_powBox_24⟩

theorem concreteZeta24_z14_maps_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkMaps
      BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.c14 = true := by
  exact BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.z14_maps_bool_sound

theorem concreteZeta24_z14_contract_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkContract
      BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.c14 = true := by
  exact BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.z14_contract_bool_sound

theorem concreteZeta24_z14_core_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkCore
      BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.c14 = true := by
  exact BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.z14_core_bool_sound

-- These rows keep the analytic meaning explicit. They are obligations, not
-- proofs of a classical zeta zero or a discharged Rho1 Krawczyk input package.
inductive ConcreteZeta24AnalyticBridgeObligation where
  | centerPowApproxFaithfulToPow
  | dyadicKrawczykSoundness
  | fixedPointTraceForConcreteNewton
  | fixedPointImpliesConcreteZero
  | concreteApproximationFaithfulToClassicalZeta
deriving DecidableEq, Repr

def concreteZeta24BridgeObligations :
    List ConcreteZeta24AnalyticBridgeObligation :=
  [ ConcreteZeta24AnalyticBridgeObligation.centerPowApproxFaithfulToPow,
    ConcreteZeta24AnalyticBridgeObligation.dyadicKrawczykSoundness,
    ConcreteZeta24AnalyticBridgeObligation.fixedPointTraceForConcreteNewton,
    ConcreteZeta24AnalyticBridgeObligation.fixedPointImpliesConcreteZero,
    ConcreteZeta24AnalyticBridgeObligation.concreteApproximationFaithfulToClassicalZeta ]

theorem concreteZeta24BridgeObligations_readback :
    concreteZeta24BridgeObligations.length = 5 := by
  rfl

structure ConcreteZeta24SoundInputSurface where
  interface_readback : concreteZeta24.zeta = { evalRat := fun _z => concreteZeta24Value }
  derivative_readback :
    concreteZeta24.zetaDerivative =
      { evalRat := fun _z => concreteZeta24DerivativeValue }
  pow_table_size : BEDC.ZetaCert.PowBoxes.powBoxes.size = 24
  coeff_table_size : BEDC.ZetaCert.Hasse24.coeffNum24.size = 24
  coeff_table_is_hasse24 :
    BEDC.ZetaCert.Hasse24.coeffNum24List =
      BEDC.ZetaCert.Hasse24.coeffNum24GenList
  zetaFormal_mem_exact_value_box :
    ∀ z : RatComplex,
      ComplexInBox
        (BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.zetaFormal
          concreteZeta24 z)
        (exactSingletonBox concreteZeta24Value)
  pow_centers_mem_boxes :
    powBoxCenterMantissaMemAt 0 ∧
      powBoxCenterMantissaMemAt 1 ∧
      powBoxCenterMantissaMemAt 2 ∧
      powBoxCenterMantissaMemAt 3 ∧
      powBoxCenterMantissaMemAt 4 ∧
      powBoxCenterMantissaMemAt 5 ∧
      powBoxCenterMantissaMemAt 6 ∧
      powBoxCenterMantissaMemAt 7 ∧
      powBoxCenterMantissaMemAt 8 ∧
      powBoxCenterMantissaMemAt 9 ∧
      powBoxCenterMantissaMemAt 10 ∧
      powBoxCenterMantissaMemAt 11 ∧
      powBoxCenterMantissaMemAt 12 ∧
      powBoxCenterMantissaMemAt 13 ∧
      powBoxCenterMantissaMemAt 14 ∧
      powBoxCenterMantissaMemAt 15 ∧
      powBoxCenterMantissaMemAt 16 ∧
      powBoxCenterMantissaMemAt 17 ∧
      powBoxCenterMantissaMemAt 18 ∧
      powBoxCenterMantissaMemAt 19 ∧
      powBoxCenterMantissaMemAt 20 ∧
      powBoxCenterMantissaMemAt 21 ∧
      powBoxCenterMantissaMemAt 22 ∧
      powBoxCenterMantissaMemAt 23
  z14_maps_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkMaps
      BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.c14 = true
  z14_contract_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkContract
      BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.c14 = true
  z14_core_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkCore
      BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.c14 = true
  bridge_obligations :
    concreteZeta24BridgeObligations =
      [ ConcreteZeta24AnalyticBridgeObligation.centerPowApproxFaithfulToPow,
        ConcreteZeta24AnalyticBridgeObligation.dyadicKrawczykSoundness,
        ConcreteZeta24AnalyticBridgeObligation.fixedPointTraceForConcreteNewton,
        ConcreteZeta24AnalyticBridgeObligation.fixedPointImpliesConcreteZero,
        ConcreteZeta24AnalyticBridgeObligation.concreteApproximationFaithfulToClassicalZeta ]

def concreteZeta24SoundInputSurface : ConcreteZeta24SoundInputSurface where
  interface_readback := rfl
  derivative_readback := rfl
  pow_table_size := concreteZeta24_pow_table_size
  coeff_table_size := concreteZeta24_coeff_table_size
  coeff_table_is_hasse24 := concreteZeta24_coeff_table_is_hasse24
  zetaFormal_mem_exact_value_box :=
    zetaFormal_concreteZeta24_mem_exact_value_box
  pow_centers_mem_boxes := powApprox24_all_centers_mem_powBoxes
  z14_maps_bool := concreteZeta24_z14_maps_bool
  z14_contract_bool := concreteZeta24_z14_contract_bool
  z14_core_bool := concreteZeta24_z14_core_bool
  bridge_obligations := rfl

theorem concreteZeta24_not_classical_zeta_claim :
    concreteZeta24BridgeObligations.length = 5 := by
  exact concreteZeta24BridgeObligations_readback

end BEDC.Derived.RHRoute.ConcreteZetaRationalInstance
