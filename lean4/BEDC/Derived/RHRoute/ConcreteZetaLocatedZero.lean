import BEDC.Derived.RHRoute.ConcreteZetaRationalInstance

set_option autoImplicit false

namespace BEDC.Derived.RHRoute.ConcreteZetaLocatedZero

open BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge
open BEDC.Derived.RHRoute.ConcreteZetaRationalInstance

abbrev ConcreteZeta24LocatedZeroStatement : Prop :=
  ∃ rho : BEDC.Derived.RHRoute.ZetaDyKrawczykDischarge.LocatedComplex,
    BEDC.Derived.RHRoute.KrawczykCertificate.LocatedInBall rho C0 R ∧
      (zetaFormal concreteZeta24).VanishesAt rho

-- This is the honest specialization of the generic discharge theorem.
-- The input package remains explicit: `concreteZeta24` is the fixed M=24
-- rational approximation from `ConcreteZetaRationalInstance`, not the
-- classical zeta function, and the faithfulness bridge is not claimed here.
theorem located_concreteZeta24_zero_near_14_1347_of_inputs
    (inputs : Rho1DischargeInputs concreteZeta24) :
    ConcreteZeta24LocatedZeroStatement := by
  exact located_zetaFormal_box_zero_near_14_1347_of_discharge_inputs inputs

structure ConcreteZeta24DischargeFrontier where
  sound_surface : ConcreteZeta24SoundInputSurface
  rho1_obligations :
    rho1DischargeRemainingObligations =
      [ Rho1DischargeRemainingObligation.powBoxFormalMembership,
        Rho1DischargeRemainingObligation.dyArithmeticSoundness,
        Rho1DischargeRemainingObligation.zeta14KernelToInterfaceBinding,
        Rho1DischargeRemainingObligation.mapsCheckerToBall,
        Rho1DischargeRemainingObligation.contractCheckerToLipschitz,
        Rho1DischargeRemainingObligation.fixedPointTrace,
        Rho1DischargeRemainingObligation.fixedPointImpliesZero,
        Rho1DischargeRemainingObligation.etaTailAndTrueZetaBridge ]
  bridge_obligations :
    concreteZeta24BridgeObligations =
      [ ConcreteZeta24AnalyticBridgeObligation.centerPowApproxFaithfulToPow,
        ConcreteZeta24AnalyticBridgeObligation.dyadicKrawczykSoundness,
        ConcreteZeta24AnalyticBridgeObligation.fixedPointTraceForConcreteNewton,
        ConcreteZeta24AnalyticBridgeObligation.fixedPointImpliesConcreteZero,
        ConcreteZeta24AnalyticBridgeObligation.concreteApproximationFaithfulToClassicalZeta ]

def concreteZeta24DischargeFrontier :
    ConcreteZeta24DischargeFrontier where
  sound_surface := concreteZeta24SoundInputSurface
  rho1_obligations := rfl
  bridge_obligations := rfl

theorem concreteZeta24_discharge_frontier_readback :
    BEDC.ZetaCert.PowBoxes.powBoxes.size = 24 ∧
      BEDC.ZetaCert.Hasse24.coeffNum24.size = 24 ∧
        concreteZeta24BridgeObligations.length = 5 ∧
          rho1DischargeRemainingObligations.length = 8 := by
  exact And.intro concreteZeta24_pow_table_size
    (And.intro concreteZeta24_coeff_table_size
      (And.intro concreteZeta24BridgeObligations_readback
        rho1DischargeRemainingObligations_readback))

end BEDC.Derived.RHRoute.ConcreteZetaLocatedZero
