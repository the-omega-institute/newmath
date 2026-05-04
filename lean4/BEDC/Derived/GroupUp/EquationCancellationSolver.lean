import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_equation_cancellation_solver {a b c d x : BHist} :
    ((GroupSingletonCarrier a -> GroupSingletonCarrier x -> GroupSingletonCarrier b ->
        (GroupSingletonClassifier (append a x) b <->
          GroupSingletonClassifier x (append BHist.Empty b))) ∧
      (GroupSingletonCarrier a -> GroupSingletonCarrier x -> GroupSingletonCarrier b ->
        (GroupSingletonClassifier (append x a) b <->
          GroupSingletonClassifier x (append b BHist.Empty))) ∧
      (GroupSingletonCarrier a -> GroupSingletonCarrier b -> GroupSingletonCarrier c ->
        GroupSingletonCarrier d ->
          (GroupSingletonClassifier (append (append a b) c) (append (append a d) c) ->
            GroupSingletonClassifier b d))) := by
  constructor
  · intro carrierA _carrierX carrierB
    constructor
    · intro classified
      have sourceSplit := append_eq_empty_iff.mp classified.left
      have targetCarrier : GroupSingletonCarrier (append BHist.Empty b) :=
        append_eq_empty_iff.mpr (And.intro (hsame_refl BHist.Empty) classified.right.left)
      exact And.intro sourceSplit.right
        (And.intro targetCarrier (hsame_trans sourceSplit.right (hsame_symm targetCarrier)))
    · intro classified
      have sourceCarrier : GroupSingletonCarrier (append a x) :=
        append_eq_empty_iff.mpr (And.intro carrierA classified.left)
      exact And.intro sourceCarrier
        (And.intro carrierB (hsame_trans sourceCarrier (hsame_symm carrierB)))
  · constructor
    · intro carrierA _carrierX carrierB
      constructor
      · intro classified
        have sourceSplit := append_eq_empty_iff.mp classified.left
        have targetCarrier : GroupSingletonCarrier (append b BHist.Empty) :=
          append_eq_empty_iff.mpr (And.intro classified.right.left (hsame_refl BHist.Empty))
        exact And.intro sourceSplit.left
          (And.intro targetCarrier (hsame_trans sourceSplit.left (hsame_symm targetCarrier)))
      · intro classified
        have sourceCarrier : GroupSingletonCarrier (append x a) :=
          append_eq_empty_iff.mpr (And.intro classified.left carrierA)
        exact And.intro sourceCarrier
          (And.intro carrierB (hsame_trans sourceCarrier (hsame_symm carrierB)))
    · intro _carrierA _carrierB _carrierC _carrierD classified
      have leftOuter := append_eq_empty_iff.mp classified.left
      have leftInner := append_eq_empty_iff.mp leftOuter.left
      have rightOuter := append_eq_empty_iff.mp classified.right.left
      have rightInner := append_eq_empty_iff.mp rightOuter.left
      exact And.intro leftInner.right
        (And.intro rightInner.right (hsame_trans leftInner.right (hsame_symm rightInner.right)))

end BEDC.Derived.GroupUp
