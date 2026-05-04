import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_append_equation_cancellation_solver {a b c d x : BHist} :
    GroupSingletonCarrier a -> GroupSingletonCarrier x -> GroupSingletonCarrier b ->
      GroupSingletonCarrier c -> GroupSingletonCarrier d ->
        ((GroupSingletonClassifier (append a x) b <->
            GroupSingletonClassifier x (append BHist.Empty b)) ∧
          (GroupSingletonClassifier (append x a) b <->
            GroupSingletonClassifier x (append b BHist.Empty)) ∧
          (GroupSingletonClassifier (append (append a b) c) (append (append a d) c) ->
            GroupSingletonClassifier b d)) := by
  intro carrierA carrierX carrierB carrierC carrierD
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have appendAX : GroupSingletonCarrier (append a x) :=
    append_eq_empty_iff.mpr (And.intro carrierA carrierX)
  have appendXA : GroupSingletonCarrier (append x a) :=
    append_eq_empty_iff.mpr (And.intro carrierX carrierA)
  have appendEmptyB : GroupSingletonCarrier (append BHist.Empty b) :=
    append_eq_empty_iff.mpr (And.intro emptyCarrier carrierB)
  have appendBEmpty : GroupSingletonCarrier (append b BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro carrierB emptyCarrier)
  constructor
  · constructor
    · intro _classified
      exact And.intro carrierX
        (And.intro appendEmptyB (hsame_trans carrierX (hsame_symm appendEmptyB)))
    · intro _classified
      exact And.intro appendAX
        (And.intro carrierB (hsame_trans appendAX (hsame_symm carrierB)))
  · constructor
    · constructor
      · intro _classified
        exact And.intro carrierX
          (And.intro appendBEmpty (hsame_trans carrierX (hsame_symm appendBEmpty)))
      · intro _classified
        exact And.intro appendXA
          (And.intro carrierB (hsame_trans appendXA (hsame_symm carrierB)))
    · intro _classified
      exact And.intro carrierB
        (And.intro carrierD (hsame_trans carrierB (hsame_symm carrierD)))

end BEDC.Derived.GroupUp
