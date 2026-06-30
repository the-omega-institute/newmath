import BEDC.Real.ZetaCert14
import BEDC.Derived.RHRoute.ZetaBoxKrawczyk

set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.ZetaDyKrawczykLift

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.KrawczykCertificate

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev LocatedComplex : Type :=
  BEDC.Derived.RHRoute.LocatedZetaZero.LocatedComplex

abbrev CFun : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.CFun

abbrev CMap : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.CMap

abbrev ZetaAnalyticInterface : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ZetaAnalyticInterface

abbrev c14 : BEDC.ZetaCert.Zeta14.Cert :=
  BEDC.ZetaCert.Zeta14.zero14Cert

abbrev C0 : RatComplex :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.C0

abbrev R : Rat :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.R

abbrev A : RatComplex :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.A

abbrev LAM : Rat :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.LAM

abbrev B0 : ClosedBall :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.B0

abbrev zetaFormal (I : ZetaAnalyticInterface) : CFun :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.zetaFormal I

abbrev rho1NewtonMap (I : ZetaAnalyticInterface) : CMap :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.rho1NewtonMap I

private theorem natLeBool_true_to_le {a b : Nat} :
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

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp
    BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

abbrev criticalZetaBoxCertificate
    (I : ZetaAnalyticInterface) : Type :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.criticalZetaBoxCertificate I

abbrev krawMapsBallLift (I : ZetaAnalyticInterface) : Prop :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.kraw_maps_ball_obligation I

abbrev krawContractLift (I : ZetaAnalyticInterface) : Prop :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.kraw_deriv_contract_obligation I

theorem zero14_checked_kernel :
    BEDC.ZetaCert.Zeta14.CertChecks c14 :=
  BEDC.ZetaCert.Zeta14.z14_checks

theorem zero14_maps_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkMaps c14 = true :=
  BEDC.ZetaCert.Zeta14.z14_maps

theorem zero14_contract_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkContract c14 = true :=
  BEDC.ZetaCert.Zeta14.z14_contract

theorem zero14_core_bool :
    BEDC.ZetaCert.Zeta14.Cert.checkCore c14 = true :=
  BEDC.ZetaCert.Zeta14.z14_checkCore

theorem zero14_bool_readback :
    BEDC.ZetaCert.Zeta14.Cert.checkMaps c14 = true ∧
      BEDC.ZetaCert.Zeta14.Cert.checkContract c14 = true ∧
        BEDC.ZetaCert.Zeta14.Cert.checkCore c14 = true := by
  exact And.intro zero14_maps_bool
    (And.intro zero14_contract_bool zero14_core_bool)

theorem zetaFormal_mem_zetaBox_of_certificate
    {I : ZetaAnalyticInterface}
    (cert : criticalZetaBoxCertificate I) :
    ∀ z : RatComplex, z ∈ B0 ->
      ComplexInBox (zetaFormal I z)
        (cert.bounds.zetaCandidate.zetaComplexBox cert.bounds.zetaOrder) :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.zetaBox_sound_ball_of_certificate
    cert

structure Rho1ContractionPropLift
    (I : ZetaAnalyticInterface) where
  box_certificate : criticalZetaBoxCertificate I
  maps_ball : krawMapsBallLift I
  contract : krawContractLift I
  fixed_implies_zero :
    ∀ z : RatComplex, z ∈ B0 ->
      rho1NewtonMap I z = z -> zetaFormal I z = ratComplexZero
  trace : BanachIterationTrace C0 R (rho1NewtonMap I) LAM

def dyKrawczykToContractionZeroCert_of_prop_lift
    {I : ZetaAnalyticInterface}
    (lift : Rho1ContractionPropLift I) :
    ContractionZeroCert (zetaFormal I) where
  c := C0
  r := R
  N := rho1NewtonMap I
  lambda := LAM
  hr := ratLtBool_true_to_ratLt (by rfl)
  hlambda0 := ratLeBool_true_to_ratLe (by rfl)
  hlambda1 := ratLtBool_true_to_ratLt (by rfl)
  maps_ball := lift.maps_ball
  contract := lift.contract
  fixed_implies_zero := lift.fixed_implies_zero
  trace := lift.trace

def rho1KrawczykCertificate_of_prop_lift
    {I : ZetaAnalyticInterface}
    (lift : Rho1ContractionPropLift I) :
    BEDC.Derived.RHRoute.ZetaBoxKrawczyk.Rho1KrawczykCertificate I where
  box_certificate := lift.box_certificate
  checker := dyKrawczykToContractionZeroCert_of_prop_lift lift
  checker_center := rfl
  checker_radius := rfl
  checker_lambda := rfl
  checker_newton_readback := fun _z => rfl

theorem maps_ball_of_prop_lift
    {I : ZetaAnalyticInterface}
    (lift : Rho1ContractionPropLift I) :
    krawMapsBallLift I :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.kraw_maps_ball_of_certificate
    (rho1KrawczykCertificate_of_prop_lift lift)

theorem contract_of_prop_lift
    {I : ZetaAnalyticInterface}
    (lift : Rho1ContractionPropLift I) :
    krawContractLift I :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.kraw_deriv_contract_of_certificate
    (rho1KrawczykCertificate_of_prop_lift lift)

theorem located_zeta_box_zero_near_14_1347_of_prop_lift
    {I : ZetaAnalyticInterface}
    (lift : Rho1ContractionPropLift I) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho C0 R ∧ (zetaFormal I).VanishesAt rho :=
  BEDC.Derived.RHRoute.ZetaBoxKrawczyk.located_zeta_box_zero_near_14_1347_of_certificate
    (rho1KrawczykCertificate_of_prop_lift lift)

inductive DyKrawczykLiftBlocker where
  | powBoxFormalMembership
  | hasse24DyadicEvaluation
  | mapsCheckerToBall
  | contractCheckerToLipschitz
  | fixedPointTrace
deriving DecidableEq, Repr

def dyKrawczykLiftBlockers : List DyKrawczykLiftBlocker :=
  [ DyKrawczykLiftBlocker.powBoxFormalMembership,
    DyKrawczykLiftBlocker.hasse24DyadicEvaluation,
    DyKrawczykLiftBlocker.mapsCheckerToBall,
    DyKrawczykLiftBlocker.contractCheckerToLipschitz,
    DyKrawczykLiftBlocker.fixedPointTrace ]

theorem dyKrawczykLiftBlockers_readback :
    dyKrawczykLiftBlockers.length = 5 := by
  decide

end BEDC.Derived.RHRoute.ZetaDyKrawczykLift
