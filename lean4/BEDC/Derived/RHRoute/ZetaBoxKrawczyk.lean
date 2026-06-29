import BEDC.Derived.RHRoute.EulerHasseEta
import BEDC.Derived.RHRoute.ZetaBoxOnBall
import BEDC.Derived.RHRoute.ZetaKrawczykInstantiation

namespace BEDC.Derived.RHRoute.ZetaBoxKrawczyk

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.KrawczykCertificate

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

abbrev RawComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaTailBounds.RawComplexBox

abbrev ZetaAnalyticInterface : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ZetaAnalyticInterface

def q (num : Int) (den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat num den

def C0 : RatComplex :=
  { re := q 1 2
    im := q 141347 10000 }

def R : Rat :=
  q 1 1000

def A : RatComplex :=
  { re := q 1245100751 1000000000
    im := q (-198244506) 1000000000 }

def LAM : Rat :=
  q 1 125

def HASSE_M : Nat :=
  96

def TAIL_START : Nat :=
  97

inductive EvalKind where
  | pointC0
  | ballB0

def zetaFormal (I : ZetaAnalyticInterface) : CFun :=
  I.zeta

def zetaFormalDeriv (I : ZetaAnalyticInterface) : CMap :=
  I.zetaDerivative

def B0 : ClosedBall :=
  Ball C0 R

def zetaBox : EvalKind -> RawComplexBox
  | EvalKind.pointC0 => BEDC.Derived.RHRoute.ZetaBoxOnBall.centerResidualRawBox
  | EvalKind.ballB0 => BEDC.Derived.RHRoute.ZetaBoxOnBall.zetaBallTubeRawBox

def zetaPrimeBox : EvalKind -> RawComplexBox
  | EvalKind.pointC0 =>
      { re := { lo := q 78329073 100000000
                hi := q 78329074 100000000 }
        im := { lo := q 12471527 100000000
                hi := q 12471528 100000000 } }
  | EvalKind.ballB0 => BEDC.Derived.RHRoute.ZetaBoxOnBall.zetaPrimeBallRawBox

def etaDepth : Nat :=
  BEDC.Derived.RHRoute.EulerHasseEta.eulerHasseDepth

def etaTailStart : Nat :=
  Nat.succ etaDepth

theorem rho1_parameters_readback :
    C0.re = q 1 2 ∧
      C0.im = q 141347 10000 ∧
      R = q 1 1000 ∧
      A.re = q 1245100751 1000000000 ∧
      A.im = q (-198244506) 1000000000 ∧
      LAM = q 1 125 ∧
      HASSE_M = 96 ∧
      TAIL_START = 97 := by
  exact
    And.intro rfl
      (And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl
              (And.intro rfl
                (And.intro rfl rfl))))))

theorem eta_depth_readback :
    etaDepth = HASSE_M ∧ etaTailStart = TAIL_START := by
  exact And.intro rfl rfl

theorem zetaBox_readback :
    zetaBox EvalKind.pointC0 =
        BEDC.Derived.RHRoute.ZetaBoxOnBall.centerResidualRawBox ∧
      zetaBox EvalKind.ballB0 =
        BEDC.Derived.RHRoute.ZetaBoxOnBall.zetaBallTubeRawBox := by
  exact And.intro rfl rfl

theorem zetaPrimeBox_readback :
    zetaPrimeBox EvalKind.ballB0 =
      BEDC.Derived.RHRoute.ZetaBoxOnBall.zetaPrimeBallRawBox := by
  rfl

def criticalZetaBoxCertificate
    (I : ZetaAnalyticInterface) : Type :=
  BEDC.Derived.RHRoute.ZetaBoxOnBall.CriticalZetaBallCertificate I

theorem zetaBox_sound_point_of_certificate
    {I : ZetaAnalyticInterface}
    (cert : criticalZetaBoxCertificate I) :
    ComplexInBox (zetaFormal I C0)
      (cert.bounds.zetaCandidate.residualComplexBox cert.bounds.zetaOrder) := by
  have hcenter : cert.bounds.zetaCandidate.center = C0 := by
    rw [cert.zetaCandidate_readback]
    rfl
  rw [← hcenter]
  exact cert.bounds.zetaSound.center_sound

theorem zetaBox_sound_ball_of_certificate
    {I : ZetaAnalyticInterface}
    (cert : criticalZetaBoxCertificate I) :
    ∀ z : RatComplex, z ∈ B0 ->
      ComplexInBox (zetaFormal I z)
        (cert.bounds.zetaCandidate.zetaComplexBox cert.bounds.zetaOrder) := by
  intro z hz
  have hcenter : cert.bounds.zetaCandidate.center = C0 := by
    rw [cert.zetaCandidate_readback]
    rfl
  have hradius : cert.bounds.zetaCandidate.radius = R := by
    rw [cert.zetaCandidate_readback]
    rfl
  exact cert.bounds.zetaSound.zeta_sound z (by
    change z ∈ Ball cert.bounds.zetaCandidate.center
      cert.bounds.zetaCandidate.radius
    rw [hcenter, hradius]
    exact hz)

theorem zetaPrimeBox_sound_ball_of_certificate
    {I : ZetaAnalyticInterface}
    (cert : criticalZetaBoxCertificate I) :
    ∀ z : RatComplex, z ∈ B0 ->
      ComplexInBox (zetaFormalDeriv I z)
        (cert.bounds.zetaPrimeCandidate.derivativeComplexBox
          cert.bounds.zetaPrimeOrder) := by
  intro z hz
  have hcenter : cert.bounds.zetaPrimeCandidate.center = C0 := by
    rw [cert.zetaPrimeCandidate_readback]
    rfl
  have hradius : cert.bounds.zetaPrimeCandidate.radius = R := by
    rw [cert.zetaPrimeCandidate_readback]
    rfl
  exact cert.bounds.zetaPrimeSound.derivative_sound z (by
    change z ∈ Ball cert.bounds.zetaPrimeCandidate.center
      cert.bounds.zetaPrimeCandidate.radius
    rw [hcenter, hradius]
    exact hz)

def rho1NewtonMap (I : ZetaAnalyticInterface) : CMap :=
  zetaNewtonMap I A

def kraw_deriv_contract_obligation
    (I : ZetaAnalyticInterface) : Prop :=
  ∀ z w : RatComplex,
    z ∈ B0 ->
      w ∈ B0 ->
        ratLe
          (dist (rho1NewtonMap I z) (rho1NewtonMap I w))
          (ratMul LAM (dist z w))

def kraw_maps_ball_obligation
    (I : ZetaAnalyticInterface) : Prop :=
  ∀ z : RatComplex, z ∈ B0 -> rho1NewtonMap I z ∈ B0

structure Rho1KrawczykCertificate
    (I : ZetaAnalyticInterface) where
  box_certificate : criticalZetaBoxCertificate I
  checker : ContractionZeroCert (zetaFormal I)
  checker_center : checker.c = C0
  checker_radius : checker.r = R
  checker_lambda : checker.lambda = LAM
  checker_newton_readback :
    ∀ z : RatComplex, checker.N z = rho1NewtonMap I z

theorem kraw_maps_ball_of_certificate
    {I : ZetaAnalyticInterface}
    (cert : Rho1KrawczykCertificate I) :
    kraw_maps_ball_obligation I := by
  intro z hz
  have hcenter : cert.checker.c = C0 := cert.checker_center
  have hradius : cert.checker.r = R := cert.checker_radius
  have hzChecker : z ∈ Ball cert.checker.c cert.checker.r := by
    rw [hcenter, hradius]
    exact hz
  have hmap := cert.checker.maps_ball z hzChecker
  have hread := cert.checker_newton_readback z
  rw [← hread]
  change cert.checker.N z ∈ Ball C0 R
  rw [← hcenter, ← hradius]
  exact hmap

theorem kraw_deriv_contract_of_certificate
    {I : ZetaAnalyticInterface}
    (cert : Rho1KrawczykCertificate I) :
    kraw_deriv_contract_obligation I := by
  intro z w hz hw
  have hcenter : cert.checker.c = C0 := cert.checker_center
  have hradius : cert.checker.r = R := cert.checker_radius
  have hlam : cert.checker.lambda = LAM := cert.checker_lambda
  have hzChecker : z ∈ Ball cert.checker.c cert.checker.r := by
    rw [hcenter, hradius]
    exact hz
  have hwChecker : w ∈ Ball cert.checker.c cert.checker.r := by
    rw [hcenter, hradius]
    exact hw
  have hcontract := cert.checker.contract z w hzChecker hwChecker
  have hzread := cert.checker_newton_readback z
  have hwread := cert.checker_newton_readback w
  rw [← hzread, ← hwread, ← hlam]
  exact hcontract

theorem located_zeta_box_zero_near_14_1347_of_certificate
    {I : ZetaAnalyticInterface}
    (cert : Rho1KrawczykCertificate I) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho C0 R ∧ (zetaFormal I).VanishesAt rho := by
  cases located_zero_of_contraction_cert cert.checker with
  | intro rho zeroData =>
      have hcenter : cert.checker.c = C0 := cert.checker_center
      have hradius : cert.checker.r = R := cert.checker_radius
      have locatedInConcrete : LocatedInBall rho C0 R := by
        rw [← hcenter, ← hradius]
        exact zeroData.left
      exact Exists.intro rho (And.intro locatedInConcrete zeroData.right)

structure AnalyticBridgeObligation
    (I : ZetaAnalyticInterface)
    (trueZeta : CFun)
    (trueZetaDerivative : CMap) where
  zeta_eq_on_B0 :
    ∀ z : RatComplex, z ∈ B0 -> zetaFormal I z = trueZeta z
  derivative_eq_on_B0 :
    ∀ z : RatComplex, z ∈ B0 ->
      zetaFormalDeriv I z = trueZetaDerivative z

theorem located_true_zeta_zero_near_14_1347_of_bridge
    {I : ZetaAnalyticInterface}
    {trueZeta : CFun}
    {trueZetaDerivative : CMap}
    (cert : Rho1KrawczykCertificate I)
    (bridge : AnalyticBridgeObligation I trueZeta trueZetaDerivative) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho C0 R ∧ trueZeta.VanishesAt rho := by
  cases located_zeta_box_zero_near_14_1347_of_certificate cert with
  | intro rho zeroData =>
      exact Exists.intro rho
        (And.intro zeroData.left
          (by
            intro n
            cases zeroData.right n with
            | intro z hz =>
                have zInBall : z ∈ B0 :=
                  zeroData.left n z hz.left
                exact Exists.intro z
                  (And.intro hz.left
                    (by
                      rw [← bridge.zeta_eq_on_B0 z zInBall]
                      exact hz.right))))

end BEDC.Derived.RHRoute.ZetaBoxKrawczyk
