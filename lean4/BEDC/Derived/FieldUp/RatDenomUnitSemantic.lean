import BEDC.Derived.FieldUp.RatDenomUnit
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

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

theorem RatDenomUnitClassifier_nonempty_rat_classifier {h k : BHist} :
    RatDenomUnitClassifier h k -> (hsame h BHist.Empty -> False) ->
      (hsame k BHist.Empty -> False) -> RatHistoryClassifier h k := by
  intro classified nonemptyH nonemptyK
  exact And.intro
    (RatDenomUnitCarrier_nonempty_rat classified.left nonemptyH)
    (And.intro
      (RatDenomUnitCarrier_nonempty_rat classified.right.left nonemptyK)
      classified.right.right)

theorem RatDenomUnitClassifier_nonempty_endpoint_iff {h k : BHist} :
    RatDenomUnitClassifier h k ->
      ((hsame h BHist.Empty -> False) ↔ (hsame k BHist.Empty -> False)) := by
  intro classified
  constructor
  · intro nonemptyH kEmpty
    exact nonemptyH (hsame_trans classified.right.right kEmpty)
  · intro nonemptyK hEmpty
    exact nonemptyK (hsame_trans (hsame_symm classified.right.right) hEmpty)

end BEDC.Derived.FieldUp
