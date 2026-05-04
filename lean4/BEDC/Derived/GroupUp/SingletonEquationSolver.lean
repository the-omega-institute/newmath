import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont

theorem GroupSingletonClassifier_append_equation_solver {a b c d x : BHist} :
    GroupSingletonCarrier a -> GroupSingletonCarrier x -> GroupSingletonCarrier b ->
    GroupSingletonCarrier c -> GroupSingletonCarrier d ->
      ((GroupSingletonClassifier (append a x) b <->
          GroupSingletonClassifier x (append BHist.Empty b)) ∧
        (GroupSingletonClassifier (append x a) b <->
          GroupSingletonClassifier x (append b BHist.Empty)) ∧
        (GroupSingletonClassifier (append (append a b) c) (append (append a d) c) ->
          GroupSingletonClassifier b d)) := by
  intro carrierA carrierX carrierB _carrierC carrierD
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have axCarrier : GroupSingletonCarrier (append a x) :=
    append_eq_empty_iff.mpr (And.intro carrierA carrierX)
  have emptyBCarrier : GroupSingletonCarrier (append BHist.Empty b) :=
    append_eq_empty_iff.mpr (And.intro emptyCarrier carrierB)
  have xaCarrier : GroupSingletonCarrier (append x a) :=
    append_eq_empty_iff.mpr (And.intro carrierX carrierA)
  have bEmptyCarrier : GroupSingletonCarrier (append b BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro carrierB emptyCarrier)
  constructor
  · constructor
    · intro _classified
      exact And.intro carrierX
        (And.intro emptyBCarrier (hsame_trans carrierX (hsame_symm emptyBCarrier)))
    · intro _classified
      exact And.intro axCarrier
        (And.intro carrierB (hsame_trans axCarrier (hsame_symm carrierB)))
  · constructor
    · constructor
      · intro _classified
        exact And.intro carrierX
          (And.intro bEmptyCarrier (hsame_trans carrierX (hsame_symm bEmptyCarrier)))
      · intro _classified
        exact And.intro xaCarrier
          (And.intro carrierB (hsame_trans xaCarrier (hsame_symm carrierB)))
    · intro _classified
      exact And.intro carrierB
        (And.intro carrierD (hsame_trans carrierB (hsame_symm carrierD)))

theorem GroupSingletonClassifier_append_equation_cancellation_solver {a b c d x : BHist} :
    GroupSingletonCarrier a -> GroupSingletonCarrier x -> GroupSingletonCarrier b ->
      GroupSingletonCarrier c -> GroupSingletonCarrier d ->
        ((GroupSingletonClassifier (append a x) b <->
            GroupSingletonClassifier x (append BHist.Empty b)) ∧
          (GroupSingletonClassifier (append x a) b <->
            GroupSingletonClassifier x (append b BHist.Empty)) ∧
          (GroupSingletonClassifier (append (append a b) c) (append (append a d) c) ->
            GroupSingletonClassifier b d)) :=
  GroupSingletonClassifier_append_equation_solver

end BEDC.Derived.GroupUp
