import BEDC.Derived.RHRoute.FarEndUnityNormalization
import BEDC.Derived.RHRoute.ZetaResonanceBoundStability

namespace BEDC.Derived.RHRoute.ZetaSolenoidBound

open BEDC.Derived.RationalUp

abbrev Rat := BEDC.Derived.RationalUp.RatNum
abbrev BoxGauge := BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge
abbrev CriticalStripInput :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput
abbrev ZetaBoxEvaluator :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaBoxEvaluator
abbrev ZetaPrecisionPacket {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) (k : Nat) :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaPrecisionPacket E k
abbrev LocatedZetaResonance {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) :=
  BEDC.Derived.RHRoute.ZetaResonanceBoundStability.LocatedZetaResonance E
abbrev ZetaResonanceBound {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s} (resonance : LocatedZetaResonance E) :=
  BEDC.Derived.RHRoute.ZetaResonanceBoundStability.ZetaResonanceBound resonance
abbrev BoundedResonancePerturbation {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s} {resonance : LocatedZetaResonance E}
    (bound : ZetaResonanceBound resonance) :=
  BEDC.Derived.RHRoute.ZetaResonanceBoundStability.BoundedResonancePerturbation
    bound
abbrev PrimeWindowNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindowNormalization
abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.UnitaryBalance.UnitaryBalanceSurface

/--
Lee-Yang 与 solenoid 只给路线语义: 本 carrier 保存有限窗口上的 zeta
packet、共振读回和单位范数归一化。圆周零点定位和解析配分函数语义留在
边界 ledger, 不在这里制造 Lean 证明。
-/
structure ZetaSolenoidObject {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) where
  precision : Nat
  packet : ZetaPrecisionPacket E precision
  packet_fits : G.fits packet.zetaBox precision
  resonance : LocatedZetaResonance E
  normalization : PrimeWindowNormalization

def solenoidZetaEnergy {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) : Rat :=
  BEDC.Derived.RHRoute.ZetaResonanceBoundStability.resonanceEnergy
    object.resonance

def solenoidUnitarySurface {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) : UnitaryBalanceSurface :=
  object.normalization.toUnitaryBalanceSurface

structure ZetaSolenoidLeeYangBound {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) where
  radius : Rat
  resonanceBound : ZetaResonanceBound object.resonance
  bound_as_radius : RatEq resonanceBound.bound radius

def solenoidBoundMargin {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    (bound : ZetaSolenoidLeeYangBound object) : Rat :=
  ratAdd bound.radius (ratNeg (solenoidZetaEnergy object))

structure LocatedZetaSolenoidBound {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s} where
  object : ZetaSolenoidObject E
  bound : ZetaSolenoidLeeYangBound object

structure ZetaSolenoidBoundedPerturbation {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    (bound : ZetaSolenoidLeeYangBound object) where
  perturbation : BoundedResonancePerturbation bound.resonanceBound

def solenoidPerturbedEnergy {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    {bound : ZetaSolenoidLeeYangBound object}
    (perturbation : ZetaSolenoidBoundedPerturbation bound) : Rat :=
  BEDC.Derived.RHRoute.ZetaResonanceBoundStability.perturbedResonanceEnergy
    perturbation.perturbation

theorem zetaSolenoid_packet_fits {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) :
    G.fits object.packet.zetaBox object.precision := by
  exact object.packet_fits

theorem zetaSolenoid_denominator_apart {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) :
    ratApart0
      (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexNormSq
        E.denominator.denominatorCenter) := by
  exact object.packet.denominator_apart

theorem zetaSolenoid_energy_nonnegative {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) :
    ratLe ratZero (solenoidZetaEnergy object) := by
  exact
    BEDC.Derived.RHRoute.ZetaResonanceBoundStability.resonanceEnergy_nonnegative
      object.resonance

theorem zetaSolenoid_radius_nonnegative {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    (bound : ZetaSolenoidLeeYangBound object) :
    ratLe ratZero bound.radius := by
  exact ratLe_respects (RatEq_refl ratZero) bound.bound_as_radius
    bound.resonanceBound.bound_nonnegative

theorem zetaSolenoid_energy_le_radius {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    (bound : ZetaSolenoidLeeYangBound object) :
    ratLe (solenoidZetaEnergy object) bound.radius := by
  exact ratLe_respects (RatEq_refl (solenoidZetaEnergy object))
    bound.bound_as_radius bound.resonanceBound.energy_le_bound

theorem zetaSolenoid_bound_margin_nonnegative {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    (bound : ZetaSolenoidLeeYangBound object) :
    ratLe ratZero (solenoidBoundMargin bound) := by
  unfold solenoidBoundMargin
  exact ratSub_nonneg_of_le (zetaSolenoid_energy_le_radius bound)

theorem zetaSolenoid_unit_norm {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) :
    RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        (solenoidUnitarySurface object).channel)
      ratOne := by
  exact object.normalization.surface_unit_norm

theorem zetaSolenoid_bound_stable {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    {bound : ZetaSolenoidLeeYangBound object}
    (perturbation : ZetaSolenoidBoundedPerturbation bound) :
    ratLe (solenoidPerturbedEnergy perturbation) bound.radius := by
  exact ratLe_respects (RatEq_refl (solenoidPerturbedEnergy perturbation))
    bound.bound_as_radius
    (BEDC.Derived.RHRoute.ZetaResonanceBoundStability.zetaResonanceBoundStable
      perturbation.perturbation)

theorem zetaSolenoid_bound_stable_with_unit_norm {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    {object : ZetaSolenoidObject E}
    {bound : ZetaSolenoidLeeYangBound object}
    (perturbation : ZetaSolenoidBoundedPerturbation bound) :
    RatEq
        (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
          (solenoidUnitarySurface object).channel)
        ratOne ∧
      ratLe (solenoidPerturbedEnergy perturbation) bound.radius := by
  exact And.intro (zetaSolenoid_unit_norm object)
    (zetaSolenoid_bound_stable perturbation)

theorem locatedZetaSolenoidBound_bounded {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    (located : LocatedZetaSolenoidBound (G := G) (s := s) (E := E)) :
    ratLe (solenoidZetaEnergy located.object) located.bound.radius := by
  exact zetaSolenoid_energy_le_radius located.bound

end BEDC.Derived.RHRoute.ZetaSolenoidBound
