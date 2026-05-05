import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem LinearMapSingletonClassifier_continuation_append_pair_classifier_iff
    {p q r s h t : BHist} :
    Cont (append p q) (append r s) h ->
      (LinearMapSingletonClassifier h t ↔
        LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q ∧
          LinearMapSingletonCarrier r ∧ LinearMapSingletonCarrier s ∧
            LinearMapSingletonCarrier t) := by
  intro continuation
  constructor
  · intro classified
    cases continuation
    have sourceParts := append_eq_empty_iff.mp classified.left
    have prefixParts := append_eq_empty_iff.mp sourceParts.left
    have targetParts := append_eq_empty_iff.mp sourceParts.right
    exact And.intro prefixParts.left
      (And.intro prefixParts.right
        (And.intro targetParts.left
          (And.intro targetParts.right classified.right.left)))
  · intro carriers
    cases continuation
    have leftCarrier : LinearMapSingletonCarrier (append p q) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carriers.right.left)
    have rightCarrier : LinearMapSingletonCarrier (append r s) :=
      append_eq_empty_iff.mpr
        (And.intro carriers.right.right.left carriers.right.right.right.left)
    have sourceCarrier : LinearMapSingletonCarrier (append (append p q) (append r s)) :=
      append_eq_empty_iff.mpr (And.intro leftCarrier rightCarrier)
    exact And.intro sourceCarrier
      (And.intro carriers.right.right.right.right
        (hsame_trans sourceCarrier (hsame_symm carriers.right.right.right.right)))

end BEDC.Derived.LinearMapUp
