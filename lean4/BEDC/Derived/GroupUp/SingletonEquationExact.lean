import BEDC.Derived.GroupUp.SingletonContext

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_left_equation_exact_iff {a x b : BHist} :
    GroupSingletonCarrier a -> GroupSingletonCarrier x -> GroupSingletonCarrier b ->
      (GroupSingletonClassifier (append a x) b <->
        GroupSingletonClassifier x (append (GroupSingletonInv a) b)) := by
  intro carrierA carrierX carrierB
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have emptyCarrier : GroupSingletonCarrier (GroupSingletonInv a) :=
      hsame_refl BHist.Empty
    have rightCarrier : GroupSingletonCarrier (append (GroupSingletonInv a) b) :=
      append_eq_empty_iff.mpr (And.intro emptyCarrier classified.right.left)
    exact And.intro leftSplit.right
      (And.intro rightCarrier (hsame_trans leftSplit.right (hsame_symm rightCarrier)))
  · intro classified
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    have leftCarrier : GroupSingletonCarrier (append a x) :=
      append_eq_empty_iff.mpr (And.intro carrierA classified.left)
    exact And.intro leftCarrier
      (And.intro rightSplit.right (hsame_trans leftCarrier (hsame_symm rightSplit.right)))

theorem GroupSingletonClassifier_right_equation_exact_iff {x a b : BHist} :
    GroupSingletonCarrier a -> GroupSingletonCarrier x -> GroupSingletonCarrier b ->
      (GroupSingletonClassifier (append x a) b <->
        GroupSingletonClassifier x (append b (GroupSingletonInv a))) := by
  intro carrierA carrierX carrierB
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have emptyCarrier : GroupSingletonCarrier (GroupSingletonInv a) :=
      hsame_refl BHist.Empty
    have rightCarrier : GroupSingletonCarrier (append b (GroupSingletonInv a)) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left emptyCarrier)
    exact And.intro leftSplit.left
      (And.intro rightCarrier (hsame_trans leftSplit.left (hsame_symm rightCarrier)))
  · intro classified
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    have leftCarrier : GroupSingletonCarrier (append x a) :=
      append_eq_empty_iff.mpr (And.intro classified.left carrierA)
    exact And.intro leftCarrier
      (And.intro rightSplit.left (hsame_trans leftCarrier (hsame_symm rightSplit.left)))

theorem GroupSingletonClassifier_two_sided_cancel {a b c d : BHist} :
    GroupSingletonCarrier a -> GroupSingletonCarrier b -> GroupSingletonCarrier c ->
      GroupSingletonCarrier d ->
      GroupSingletonClassifier (append (append a b) c) (append (append a d) c) ->
        GroupSingletonClassifier b d := by
  intro _carrierA carrierB _carrierC carrierD classified
  have sameLeftProducts : hsame (append a b) (append a d) :=
    append_right_cancel (k := c) classified.right.right
  have sameMiddle : hsame b d :=
    append_left_cancel (h := a) sameLeftProducts
  exact And.intro carrierB (And.intro carrierD sameMiddle)

theorem GroupSingletonClassifier_equation_solver_determinacy {a b c d x y : BHist} :
    GroupSingletonCarrier a -> GroupSingletonCarrier b -> GroupSingletonCarrier c ->
    GroupSingletonCarrier d -> GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      ((GroupSingletonClassifier (append a x) b ->
          GroupSingletonClassifier (append a y) b -> GroupSingletonClassifier x y) ∧
        (GroupSingletonClassifier (append x a) b ->
          GroupSingletonClassifier (append y a) b -> GroupSingletonClassifier x y) ∧
        (GroupSingletonClassifier (append (append a x) c) d ->
          GroupSingletonClassifier (append (append a y) c) d ->
            GroupSingletonClassifier x y)) := by
  intro carrierA carrierB carrierC _carrierD carrierX carrierY
  constructor
  · intro classifiedX classifiedY
    have solvedX : GroupSingletonClassifier x (append (GroupSingletonInv a) b) :=
      (GroupSingletonClassifier_left_equation_exact_iff carrierA carrierX carrierB).mp
        classifiedX
    have solvedY : GroupSingletonClassifier y (append (GroupSingletonInv a) b) :=
      (GroupSingletonClassifier_left_equation_exact_iff carrierA carrierY carrierB).mp
        classifiedY
    exact And.intro carrierX
      (And.intro carrierY (hsame_trans solvedX.right.right (hsame_symm solvedY.right.right)))
  · constructor
    · intro classifiedX classifiedY
      have solvedX : GroupSingletonClassifier x (append b (GroupSingletonInv a)) :=
        (GroupSingletonClassifier_right_equation_exact_iff carrierA carrierX carrierB).mp
          classifiedX
      have solvedY : GroupSingletonClassifier y (append b (GroupSingletonInv a)) :=
        (GroupSingletonClassifier_right_equation_exact_iff carrierA carrierY carrierB).mp
          classifiedY
      exact And.intro carrierX
        (And.intro carrierY
          (hsame_trans solvedX.right.right (hsame_symm solvedY.right.right)))
    · intro classifiedX classifiedY
      have sameProducts :
          hsame (append (append a x) c) (append (append a y) c) :=
        hsame_trans classifiedX.right.right (hsame_symm classifiedY.right.right)
      have productClassifier :
          GroupSingletonClassifier (append (append a x) c) (append (append a y) c) :=
        And.intro classifiedX.left (And.intro classifiedY.left sameProducts)
      exact GroupSingletonClassifier_two_sided_cancel carrierA carrierX carrierC carrierY
        productClassifier

end BEDC.Derived.GroupUp
