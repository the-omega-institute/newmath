import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.HomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def HomologySingletonCycleCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def HomologySingletonCycleClassifier (h k : BHist) : Prop :=
  HomologySingletonCycleCarrier h ∧ HomologySingletonCycleCarrier k ∧ hsame h k

theorem HomologySingletonCycle_semanticNameCert :
    SemanticNameCert HomologySingletonCycleCarrier HomologySingletonCycleCarrier
      HomologySingletonCycleCarrier HomologySingletonCycleClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _carrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.HomologyUp
