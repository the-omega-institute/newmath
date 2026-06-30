import BEDC.Derived.RHRoute.ZetaDyKrawczykLift

set_option autoImplicit false

namespace BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge

open BEDC.Derived.RHRoute.KrawczykCertificate

abbrev Rat : Type :=
  BEDC.Derived.RationalUp.RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev LocatedComplex : Type :=
  BEDC.Derived.RHRoute.LocatedZetaZero.LocatedComplex

abbrev ZetaAnalyticInterface : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ZetaAnalyticInterface

abbrev Rho1ContractionPropLift (I : ZetaAnalyticInterface) : Type :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.Rho1ContractionPropLift I

abbrev criticalZetaBoxCertificate (I : ZetaAnalyticInterface) : Type :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.criticalZetaBoxCertificate I

abbrev krawMapsBallLift (I : ZetaAnalyticInterface) : Prop :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.krawMapsBallLift I

abbrev krawContractLift (I : ZetaAnalyticInterface) : Prop :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.krawContractLift I

abbrev C0 : RatComplex :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.C0

abbrev R : Rat :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.R

abbrev B0 : ClosedBall :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.B0

abbrev LAM : Rat :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.LAM

abbrev c14 : BEDC.ZetaCert.Zeta14.Cert :=
  BEDC.ZetaCert.Zeta14.zero14Cert

abbrev zetaFormal (I : ZetaAnalyticInterface) : CFun :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.zetaFormal I

abbrev rho1NewtonMap (I : ZetaAnalyticInterface) : CMap :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.rho1NewtonMap I

-- The Zeta14 checker is a finite M=24 Hasse kernel. This module does
-- not identify that kernel with an arbitrary analytic interface `I.zeta`.
def zeta14BoolKernelDepth : Nat :=
  24

theorem zeta14BoolKernelDepth_readback :
    zeta14BoolKernelDepth = 24 := by
  rfl

structure Zeta14BoolKernelDischarge where
  checks : BEDC.ZetaCert.Zeta14.CertChecks c14
  maps_bool : BEDC.ZetaCert.Zeta14.Cert.checkMaps c14 = true
  contract_bool : BEDC.ZetaCert.Zeta14.Cert.checkContract c14 = true
  core_bool : BEDC.ZetaCert.Zeta14.Cert.checkCore c14 = true
  hasse_kernel_depth : Nat
  hasse_kernel_depth_readback : hasse_kernel_depth = 24

def zeta14BoolKernelDischarge : Zeta14BoolKernelDischarge where
  checks := BEDC.Derived.RHRoute.ZetaDyKrawczykLift.zero14_checked_kernel
  maps_bool := BEDC.Derived.RHRoute.ZetaDyKrawczykLift.zero14_maps_bool
  contract_bool := BEDC.Derived.RHRoute.ZetaDyKrawczykLift.zero14_contract_bool
  core_bool := BEDC.Derived.RHRoute.ZetaDyKrawczykLift.zero14_core_bool
  hasse_kernel_depth := zeta14BoolKernelDepth
  hasse_kernel_depth_readback := zeta14BoolKernelDepth_readback

theorem z14_maps_bool_sound :
    BEDC.ZetaCert.Zeta14.Cert.checkMaps c14 = true :=
  zeta14BoolKernelDischarge.maps_bool

theorem z14_contract_bool_sound :
    BEDC.ZetaCert.Zeta14.Cert.checkContract c14 = true :=
  zeta14BoolKernelDischarge.contract_bool

theorem z14_core_bool_sound :
    BEDC.ZetaCert.Zeta14.Cert.checkCore c14 = true :=
  zeta14BoolKernelDischarge.core_bool

theorem z14_kernel_depth_sound :
    zeta14BoolKernelDischarge.hasse_kernel_depth = 24 :=
  zeta14BoolKernelDischarge.hasse_kernel_depth_readback

def z14MapsBallRadiusX : Int :=
  let q := BEDC.ZetaCert.Zeta14.Cert.q c14
  let radiusMatrix := BEDC.ZetaCert.Zeta14.Cert.R c14
  BEDC.ZetaCert.Dy.mag q.x +
    BEDC.ZetaCert.Zeta14.rowBallBound
      (BEDC.ZetaCert.Zeta14.M2.row0Mag radiusMatrix) c14.rad

def z14MapsBallRadiusY : Int :=
  let q := BEDC.ZetaCert.Zeta14.Cert.q c14
  let radiusMatrix := BEDC.ZetaCert.Zeta14.Cert.R c14
  BEDC.ZetaCert.Dy.mag q.y +
    BEDC.ZetaCert.Zeta14.rowBallBound
      (BEDC.ZetaCert.Zeta14.M2.row1Mag radiusMatrix) c14.rad

theorem z14_maps_checker_integer_sound :
    z14MapsBallRadiusX <= c14.rad ∧
      z14MapsBallRadiusY <= c14.rad := by
  unfold z14MapsBallRadiusX z14MapsBallRadiusY
  have h := z14_maps_bool_sound
  unfold BEDC.ZetaCert.Zeta14.Cert.checkMaps
    BEDC.ZetaCert.Zeta14.mapsBallInf at h
  exact of_decide_eq_true h

theorem z14_contract_checker_integer_sound :
    125 *
        BEDC.ZetaCert.Zeta14.M2.opMagInf
          (BEDC.ZetaCert.Zeta14.Cert.R c14) <=
      BEDC.ZetaCert.Dy.S := by
  have h := z14_contract_bool_sound
  unfold BEDC.ZetaCert.Zeta14.Cert.checkContract
    BEDC.ZetaCert.Zeta14.M2.contract125 at h
  exact BEDC.ZetaCert.Dy.leInv125_sound h

structure Rho1DischargeInputs (I : ZetaAnalyticInterface) where
  box_certificate : criticalZetaBoxCertificate I
  maps_ball_of_maps_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkMaps c14 = true ->
      krawMapsBallLift I
  contract_of_contract_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkContract c14 = true ->
      krawContractLift I
  fixed_implies_zero :
    ∀ z : RatComplex, z ∈ B0 ->
      rho1NewtonMap I z = z -> zetaFormal I z = ratComplexZero
  trace : BanachIterationTrace C0 R (rho1NewtonMap I) LAM

def discharge_Rho1ContractionPropLift_of_inputs
    {I : ZetaAnalyticInterface}
    (inputs : Rho1DischargeInputs I) :
    Rho1ContractionPropLift I where
  box_certificate := inputs.box_certificate
  maps_ball := inputs.maps_ball_of_maps_bool z14_maps_bool_sound
  contract := inputs.contract_of_contract_bool z14_contract_bool_sound
  fixed_implies_zero := inputs.fixed_implies_zero
  trace := inputs.trace

theorem z14_maps_ball_sound_of_inputs
    {I : ZetaAnalyticInterface}
    (inputs : Rho1DischargeInputs I) :
    krawMapsBallLift I :=
  (discharge_Rho1ContractionPropLift_of_inputs inputs).maps_ball

theorem z14_contract_sound_of_inputs
    {I : ZetaAnalyticInterface}
    (inputs : Rho1DischargeInputs I) :
    krawContractLift I :=
  (discharge_Rho1ContractionPropLift_of_inputs inputs).contract

theorem zetaFormal_mem_certificate_zetaBox_of_discharge_inputs
    {I : ZetaAnalyticInterface}
    (inputs : Rho1DischargeInputs I) :
    ∀ z : RatComplex, z ∈ B0 ->
      ComplexInBox (zetaFormal I z)
        (inputs.box_certificate.bounds.zetaCandidate.zetaComplexBox
          inputs.box_certificate.bounds.zetaOrder) :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.zetaFormal_mem_zetaBox_of_certificate
    inputs.box_certificate

-- This is conditional on the Prop-level inputs above. The theorem does
-- not assert a zero of the classical zeta function.
theorem located_zetaFormal_box_zero_near_14_1347_of_discharge_inputs
    {I : ZetaAnalyticInterface}
    (inputs : Rho1DischargeInputs I) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho C0 R ∧ (zetaFormal I).VanishesAt rho :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.located_zeta_box_zero_near_14_1347_of_prop_lift
    (discharge_Rho1ContractionPropLift_of_inputs inputs)

theorem located_zetaFormal_box_zero_near_14_1347_of_prop_lift
    {I : ZetaAnalyticInterface}
    (lift : Rho1ContractionPropLift I) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho C0 R ∧ (zetaFormal I).VanishesAt rho :=
  BEDC.Derived.RHRoute.ZetaDyKrawczykLift.located_zeta_box_zero_near_14_1347_of_prop_lift
    lift

inductive Rho1DischargeRemainingObligation where
  | powBoxFormalMembership
  | dyArithmeticSoundness
  | zeta14KernelToInterfaceBinding
  | mapsCheckerToBall
  | contractCheckerToLipschitz
  | fixedPointTrace
  | fixedPointImpliesZero
  | etaTailAndTrueZetaBridge
deriving DecidableEq, Repr

def rho1DischargeRemainingObligations :
    List Rho1DischargeRemainingObligation :=
  [ Rho1DischargeRemainingObligation.powBoxFormalMembership,
    Rho1DischargeRemainingObligation.dyArithmeticSoundness,
    Rho1DischargeRemainingObligation.zeta14KernelToInterfaceBinding,
    Rho1DischargeRemainingObligation.mapsCheckerToBall,
    Rho1DischargeRemainingObligation.contractCheckerToLipschitz,
    Rho1DischargeRemainingObligation.fixedPointTrace,
    Rho1DischargeRemainingObligation.fixedPointImpliesZero,
    Rho1DischargeRemainingObligation.etaTailAndTrueZetaBridge ]

theorem rho1DischargeRemainingObligations_readback :
    rho1DischargeRemainingObligations.length = 8 := by
  decide

end BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge
