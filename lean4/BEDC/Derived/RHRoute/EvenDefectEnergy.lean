import BEDC.Derived.RHRoute.PrimeSkewDefect
import BEDC.Derived.RationalUp.MetricOrder

namespace BEDC.Derived.RHRoute.EvenDefectEnergy

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.PrimeSkewDefect

abbrev RatNum := BEDC.Derived.RationalUp.RatNum

structure EvenDefectEnergy where
  defect : RatNum
  energy : RatNum
  energy_eq_magnitude : RatEq energy (ratMagnitude defect)

def evenDefectEnergy (defect : RatNum) : EvenDefectEnergy where
  defect := defect
  energy := ratMagnitude defect
  energy_eq_magnitude := RatEq_refl _

def evenDefectEnergyValue (defect : RatNum) : RatNum :=
  (evenDefectEnergy defect).energy

theorem evenDefectEnergyValue_eq_magnitude (defect : RatNum) :
    RatEq (evenDefectEnergyValue defect) (ratMagnitude defect) := by
  exact RatEq_refl _

theorem evenDefectEnergy_nonnegative (defect : RatNum) :
    ratLe ratZero (evenDefectEnergyValue defect) := by
  exact ratMagnitude_nonneg defect

structure LocatedEvenDefectEnergy where
  support : Nat
  defect : RatNum
  packet : EvenDefectEnergy
  packet_matches_defect : RatEq packet.defect defect

def locatedEvenDefectEnergy (support : Nat) (defect : RatNum) :
    LocatedEvenDefectEnergy where
  support := support
  defect := defect
  packet := evenDefectEnergy defect
  packet_matches_defect := RatEq_refl _

def mirrorSkewEvenEnergy {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) : EvenDefectEnergy :=
  evenDefectEnergy cert.mirrorSkew

def mirrorSkewLocatedEvenEnergy {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) : LocatedEvenDefectEnergy :=
  locatedEvenDefectEnergy cert.prime cert.mirrorSkew

theorem mirrorSkewEvenEnergy_defect {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    RatEq (mirrorSkewEvenEnergy cert).defect cert.mirrorSkew := by
  exact RatEq_refl _

theorem mirrorSkewEvenEnergy_nonnegative {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    ratLe ratZero (mirrorSkewEvenEnergy cert).energy := by
  exact ratMagnitude_nonneg cert.mirrorSkew

theorem mirrorSkewLocatedEvenEnergy_support_prime
    {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime
      (mirrorSkewLocatedEvenEnergy cert).support := by
  exact cert.source_prime

theorem oddDefect_dual_evenEnergy {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    RatEq (mirrorSkewEvenEnergy cert).energy
      (ratMagnitude (mirrorAmplitudeSkew channels cert.prime)) := by
  exact RatEq_refl _

end BEDC.Derived.RHRoute.EvenDefectEnergy
