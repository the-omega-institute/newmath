import BEDC.Derived.RHRoute.EvenDefectEnergy
import BEDC.Derived.RHRoute.UnitaryBalance
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.RHRoute.ZetaResonanceBoundStability

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
abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.UnitaryBalance.UnitaryBalanceSurface
abbrev EvenDefectEnergy :=
  BEDC.Derived.RHRoute.EvenDefectEnergy.EvenDefectEnergy
abbrev LocatedEvenDefectEnergy :=
  BEDC.Derived.RHRoute.EvenDefectEnergy.LocatedEvenDefectEnergy

-- “Resonance” 与 “energy” 是路线命名和有理账本语言；
-- 核对象只是带有有理界、有限通道范数和 zeta box evaluator 精度包的 located 记录。
structure LocatedZetaResonance {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) where
  precision : Nat
  packet : ZetaPrecisionPacket E precision
  packet_fits : G.fits packet.zetaBox precision
  balance : UnitaryBalanceSurface
  energy : LocatedEvenDefectEnergy

def resonanceEnergy {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (resonance : LocatedZetaResonance E) : Rat :=
  resonance.energy.packet.energy

structure ZetaResonanceBound {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (resonance : LocatedZetaResonance E) where
  bound : Rat
  bound_nonnegative : ratLe ratZero bound
  energy_le_bound : ratLe (resonanceEnergy resonance) bound

def resonanceRemainingMargin {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (resonance : LocatedZetaResonance E)
    (bound : ZetaResonanceBound resonance) : Rat :=
  ratAdd bound.bound (ratNeg (resonanceEnergy resonance))

structure BoundedResonancePerturbation {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    {resonance : LocatedZetaResonance E}
    (bound : ZetaResonanceBound resonance) where
  defect : Rat
  energy : EvenDefectEnergy
  energy_matches_defect : RatEq energy.defect defect
  energy_nonnegative : ratLe ratZero energy.energy
  perturbed_energy_le_bound :
    ratLe (ratAdd (resonanceEnergy resonance) energy.energy) bound.bound

def perturbedResonanceEnergy {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {resonance : LocatedZetaResonance E}
    {bound : ZetaResonanceBound resonance}
    (perturbation : BoundedResonancePerturbation bound) : Rat :=
  ratAdd (resonanceEnergy resonance) perturbation.energy.energy

theorem resonanceEnergy_nonnegative {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (resonance : LocatedZetaResonance E) :
    ratLe ratZero (resonanceEnergy resonance) := by
  exact ratLe_respects (RatEq_refl ratZero)
    (RatEq_symm resonance.energy.packet.energy_eq_magnitude)
    (ratMagnitude_nonneg resonance.energy.packet.defect)

theorem resonanceBound_has_nonnegative_margin
    {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {resonance : LocatedZetaResonance E}
    (bound : ZetaResonanceBound resonance) :
    ratLe ratZero (resonanceRemainingMargin resonance bound) := by
  unfold resonanceRemainingMargin
  exact ratSub_nonneg_of_le bound.energy_le_bound

theorem boundedPerturbation_energy_nonnegative
    {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {resonance : LocatedZetaResonance E}
    {bound : ZetaResonanceBound resonance}
    (perturbation : BoundedResonancePerturbation bound) :
    ratLe ratZero perturbation.energy.energy := by
  exact perturbation.energy_nonnegative

theorem boundedPerturbation_energy_le_bound
    {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {resonance : LocatedZetaResonance E}
    {bound : ZetaResonanceBound resonance}
    (perturbation : BoundedResonancePerturbation bound) :
    ratLe (perturbedResonanceEnergy perturbation) bound.bound := by
  exact perturbation.perturbed_energy_le_bound

theorem zetaResonanceBoundStable
    {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {resonance : LocatedZetaResonance E}
    {bound : ZetaResonanceBound resonance}
    (perturbation : BoundedResonancePerturbation bound) :
    ratLe (perturbedResonanceEnergy perturbation) bound.bound := by
  exact boundedPerturbation_energy_le_bound perturbation

theorem zetaResonanceBoundStable_with_balance
    {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    {resonance : LocatedZetaResonance E}
    {bound : ZetaResonanceBound resonance}
    (perturbation : BoundedResonancePerturbation bound) :
    RatEq
        (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
          resonance.balance.channel)
        ratOne ∧
      ratLe (perturbedResonanceEnergy perturbation) bound.bound := by
  exact And.intro resonance.balance.norm_one
    (zetaResonanceBoundStable perturbation)

theorem locatedZetaResonance_packet_fits
    {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (resonance : LocatedZetaResonance E) :
    G.fits resonance.packet.zetaBox resonance.precision := by
  exact resonance.packet_fits

theorem locatedZetaResonance_denominator_apart
    {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (resonance : LocatedZetaResonance E) :
    ratApart0
      (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexNormSq
        E.denominator.denominatorCenter) := by
  exact resonance.packet.denominator_apart

end BEDC.Derived.RHRoute.ZetaResonanceBoundStability
