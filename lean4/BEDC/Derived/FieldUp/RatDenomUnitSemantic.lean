import BEDC.Derived.FieldUp.RatDenomUnit
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RatDenomUnitClassifier_semanticNameCert :
    SemanticNameCert RatDenomUnitCarrier RatDenomUnitCarrier RatDenomUnitCarrier
      RatDenomUnitClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (Or.inl (hsame_refl BHist.Empty))
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
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.FieldUp
