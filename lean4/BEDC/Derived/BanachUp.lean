import BEDC.Derived.MetricUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.BanachUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.MetricUp
open BEDC.Derived.VecSpaceUp

def BanachSingletonCarrier (h : BHist) : Prop :=
  VecSpaceSingletonCarrier h ∧ MetricDistanceWitness h BHist.Empty BHist.Empty

def BanachSingletonClassifier (h k : BHist) : Prop :=
  BanachSingletonCarrier h ∧ BanachSingletonCarrier k ∧ hsame h k

theorem BanachSingletonCarrier_semanticNameCert :
    SemanticNameCert BanachSingletonCarrier BanachSingletonCarrier BanachSingletonCarrier
      BanachSingletonClassifier := by
  have emptyMetric : MetricDistanceWitness BHist.Empty BHist.Empty BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := BHist.Empty) (y := BHist.Empty)).mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have emptyCarrier : BanachSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) emptyMetric
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k same
        exact And.intro same.right.left
          (And.intro same.left (hsame_symm same.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro _h _k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

end BEDC.Derived.BanachUp
