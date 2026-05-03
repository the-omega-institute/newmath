import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_continuation_append_split_iff {L P Q R T : BHist} :
    Cont P Q T ->
      (FieldSingletonClassifier (append L T) R <->
        FieldSingletonCarrier L /\ FieldSingletonCarrier P /\ FieldSingletonCarrier Q /\
          FieldSingletonCarrier R) := by
  intro continuation
  constructor
  · intro classified
    have appendEmpty := append_eq_empty_iff.mp classified.left
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation appendEmpty.right
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro appendEmpty.left
      (And.intro endpoints.left (And.intro endpoints.right classified.right.left))
  · intro carriers
    have carrierT : FieldSingletonCarrier T :=
      hsame_trans continuation
        (append_eq_empty_iff.mpr (And.intro carriers.right.left carriers.right.right.left))
    have leftCarrier : FieldSingletonCarrier (append L T) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carrierT)
    exact And.intro leftCarrier
      (And.intro carriers.right.right.right
        (hsame_trans leftCarrier (hsame_symm carriers.right.right.right)))

theorem FieldSingletonClassifier_continuation_append_context_split_iff
    {L P Q T R S : BHist} :
    Cont P Q T ->
      (FieldSingletonClassifier (append L T) (append R S) <->
        FieldSingletonCarrier L ∧ FieldSingletonCarrier P ∧ FieldSingletonCarrier Q ∧
          FieldSingletonCarrier R ∧ FieldSingletonCarrier S) := by
  intro continuation
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation leftSplit.right
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro leftSplit.left
      (And.intro endpoints.left
        (And.intro endpoints.right (And.intro rightSplit.left rightSplit.right)))
  · intro carriers
    have carrierT : FieldSingletonCarrier T :=
      hsame_trans continuation
        (append_eq_empty_iff.mpr (And.intro carriers.right.left carriers.right.right.left))
    have leftCarrier : FieldSingletonCarrier (append L T) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carrierT)
    have rightCarrier : FieldSingletonCarrier (append R S) :=
      append_eq_empty_iff.mpr (And.intro carriers.right.right.right.left
        carriers.right.right.right.right)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem FieldSingletonClassifier_continuation_context_empty_result_iff {L R P Q T : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      Cont (append L P) (append Q R) T ->
        (FieldSingletonClassifier T BHist.Empty <-> FieldSingletonClassifier P Q) := by
  intro carrierL carrierR continuation
  constructor
  · intro classified
    have emptyContinuation : Cont (append L P) (append Q R) BHist.Empty :=
      cont_result_hsame_transport continuation classified.left
    have emptyParts := cont_empty_result_inversion emptyContinuation
    have leftSplit := append_eq_empty_iff.mp emptyParts.left
    have rightSplit := append_eq_empty_iff.mp emptyParts.right
    exact And.intro leftSplit.right
      (And.intro rightSplit.left (hsame_trans leftSplit.right (hsame_symm rightSplit.left)))
  · intro classified
    have leftEmpty : hsame (append L P) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro carrierL classified.left)
    have rightEmpty : hsame (append Q R) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierR)
    have resultEmpty : FieldSingletonCarrier T :=
      hsame_trans continuation (append_eq_empty_iff.mpr (And.intro leftEmpty rightEmpty))
    exact And.intro resultEmpty
      (And.intro (hsame_refl BHist.Empty) resultEmpty)

theorem FieldSingletonClassifier_continuation_result_context_iff {L R P Q T : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> Cont P Q T ->
      (FieldSingletonClassifier (append L (append T R)) BHist.Empty <->
        FieldSingletonCarrier P ∧ FieldSingletonCarrier Q) := by
  intro carrierL carrierR continuation
  constructor
  · intro classified
    have outerSplit := append_eq_empty_iff.mp classified.left
    have innerSplit := append_eq_empty_iff.mp outerSplit.right
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation innerSplit.left
    exact cont_empty_result_inversion emptyContinuation
  · intro endpoints
    have resultCarrier : FieldSingletonCarrier T :=
      hsame_trans continuation (append_eq_empty_iff.mpr endpoints)
    have innerCarrier : FieldSingletonCarrier (append T R) :=
      append_eq_empty_iff.mpr (And.intro resultCarrier carrierR)
    have outerCarrier : FieldSingletonCarrier (append L (append T R)) :=
      append_eq_empty_iff.mpr (And.intro carrierL innerCarrier)
    exact And.intro outerCarrier
      (And.intro (hsame_refl BHist.Empty) outerCarrier)

end BEDC.Derived.FieldUp
