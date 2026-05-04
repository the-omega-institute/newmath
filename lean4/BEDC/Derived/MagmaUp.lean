import BEDC.FKernel.Unary
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MagmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

theorem concrete_unary_history_magma_cont_laws :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let mul : BHist -> BHist -> BHist := append
    (∀ {h k : BHist}, Carrier h -> Carrier k -> Carrier (mul h k) ∧ Cont h k (mul h k)) ∧
      (∀ {h h' k k' r r' : BHist}, Classifier h h' -> Classifier k k' ->
        Cont h k r -> Cont h' k' r' -> Classifier r r') := by
  dsimp
  constructor
  · intro h k unaryH unaryK
    exact And.intro (unary_append_closed unaryH unaryK) (cont_intro rfl)
  · intro h h' k k' r r' classifiedH classifiedK hcont hcont'
    have unaryR : UnaryHistory r :=
      unary_cont_closed classifiedH.left classifiedK.left hcont
    have unaryR' : UnaryHistory r' :=
      unary_cont_closed classifiedH.right.left classifiedK.right.left hcont'
    have sameR : hsame r r' :=
      cont_respects_hsame classifiedH.right.right classifiedK.right.right hcont hcont'
    exact And.intro unaryR (And.intro unaryR' sameR)

theorem concrete_unary_history_magma_classifier_stability :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    (∀ {h : BHist}, Carrier h -> Classifier h h) ∧
      (∀ {h k : BHist}, Classifier h k -> Classifier k h) ∧
        (∀ {h k l : BHist}, Classifier h k -> Classifier k l -> Classifier h l) ∧
          (∀ {h k : BHist}, Classifier h k -> Carrier h ∧ Carrier k) := by
  dsimp
  constructor
  · intro h carrierH
    exact And.intro carrierH (And.intro carrierH (hsame_refl h))
  · constructor
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · constructor
      · intro h k l classifiedHK classifiedKL
        exact And.intro classifiedHK.left
          (And.intro classifiedKL.right.left
            (hsame_trans classifiedHK.right.right classifiedKL.right.right))
      · intro h k classified
        exact And.intro classified.left classified.right.left

theorem ConcreteUnaryHistoryMagma_semanticNameCert :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    SemanticNameCert Carrier Carrier Carrier Classifier ∧
      (∀ {h k : BHist}, Carrier h -> Carrier k ->
        Carrier (append h k) ∧ Cont h k (append h k)) ∧
      (∀ {h h' k k' r r' : BHist}, Classifier h h' -> Classifier k k' ->
        Cont h k r -> Cont h' k' r' -> Classifier r r') := by
  dsimp
  constructor
  · constructor
    · constructor
      · exact Exists.intro BHist.Empty unary_empty
      · intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      · intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      · intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      · intro h k classified _carrier
        exact classified.right.left
    · intro h source
      exact source
    · intro h source
      exact source
  · exact concrete_unary_history_magma_cont_laws

theorem concrete_unary_history_magma_cont_result_unary_iff {h k r : BHist} :
    Cont h k r -> (UnaryHistory r ↔ UnaryHistory h ∧ UnaryHistory k) := by
  intro rel
  constructor
  · intro resultCarrier
    have appendedCarrier : UnaryHistory (append h k) := by
      cases rel
      exact resultCarrier
    exact unary_append_factors_iff_result.mpr appendedCarrier
  · intro factors
    cases rel
    exact unary_append_factors_iff_result.mp factors

theorem concrete_unary_history_magma_classifier_append_factors_iff {h h' k k' : BHist} :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
    Classifier (append h k) (append h' k') ↔
      Carrier h ∧ Carrier k ∧ Carrier h' ∧ Carrier k' ∧
        hsame (append h k) (append h' k') := by
  dsimp
  constructor
  · intro classified
    have leftFactors :
        UnaryHistory h ∧ UnaryHistory k :=
      (unary_append_factors_iff_result (h := h) (k := k)).mpr classified.left
    have rightFactors :
        UnaryHistory h' ∧ UnaryHistory k' :=
      (unary_append_factors_iff_result (h := h') (k := k')).mpr classified.right.left
    exact And.intro leftFactors.left
      (And.intro leftFactors.right
        (And.intro rightFactors.left
          (And.intro rightFactors.right classified.right.right)))
  · intro factors
    have leftCarrier : UnaryHistory (append h k) :=
      unary_append_closed factors.left factors.right.left
    have rightCarrier : UnaryHistory (append h' k') :=
      unary_append_closed factors.right.right.left factors.right.right.right.left
    exact And.intro leftCarrier
      (And.intro rightCarrier factors.right.right.right.right)

theorem concrete_unary_history_magma_classifier_append_empty_endpoints_iff {h k : BHist} :
    (let Carrier : BHist -> Prop := UnaryHistory
     let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
     Classifier (append h k) BHist.Empty ↔ hsame h BHist.Empty ∧ hsame k BHist.Empty) := by
  dsimp
  constructor
  · intro classified
    exact append_eq_empty_iff.mp classified.right.right
  · intro endpoints
    have appendCarrier : UnaryHistory (append h k) := by
      cases endpoints.left
      cases endpoints.right
      exact unary_empty
    exact And.intro appendCarrier (And.intro unary_empty (append_eq_empty_iff.mpr endpoints))

theorem concrete_unary_history_magma_cont_result_classifier_factors_iff
    {h h' k k' r r' : BHist} :
    Cont h k r -> Cont h' k' r' ->
      (let Carrier : BHist -> Prop := UnaryHistory
       let Classifier : BHist -> BHist -> Prop :=
        fun x y => Carrier x ∧ Carrier y ∧ hsame x y
       Classifier r r' ↔
        Carrier h ∧ Carrier k ∧ Carrier h' ∧ Carrier k' ∧ hsame r r') := by
  intro left right
  cases left
  cases right
  exact concrete_unary_history_magma_classifier_append_factors_iff

theorem concrete_unary_history_magma_classifier_append_middle_cancel_iff
    {left middle middle' right : BHist} :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
    Carrier left -> Carrier right ->
      (Classifier (append left (append middle right)) (append left (append middle' right)) ↔
        Carrier middle ∧ Carrier middle' ∧ hsame middle middle') := by
  dsimp
  intro leftCarrier rightCarrier
  constructor
  · intro classified
    have middleCarrier : UnaryHistory middle :=
      (unary_append_context_middle_iff leftCarrier rightCarrier).mp classified.left
    have middleCarrier' : UnaryHistory middle' :=
      (unary_append_context_middle_iff leftCarrier rightCarrier).mp classified.right.left
    have sameWithRight : hsame (append middle right) (append middle' right) :=
      append_left_cancel (h := left) classified.right.right
    have sameMiddle : hsame middle middle' :=
      append_right_cancel (k := right) sameWithRight
    exact And.intro middleCarrier (And.intro middleCarrier' sameMiddle)
  · intro core
    have leftResultCarrier : UnaryHistory (append left (append middle right)) :=
      unary_append_closed leftCarrier (unary_append_closed core.left rightCarrier)
    have rightResultCarrier : UnaryHistory (append left (append middle' right)) :=
      unary_append_closed leftCarrier (unary_append_closed core.right.left rightCarrier)
    have sameResult :
        hsame (append left (append middle right)) (append left (append middle' right)) := by
      cases core.right.right
      rfl
    exact And.intro leftResultCarrier (And.intro rightResultCarrier sameResult)

theorem concrete_unary_history_magma_classifier_append_rotated_middle_cancel_iff
    {left middle middle' right : BHist} :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
    Carrier left -> Carrier right ->
      (Classifier (append left (append middle right)) (append (append left middle') right) <->
        Carrier middle ∧ Carrier middle' ∧ hsame middle middle') := by
  dsimp
  intro leftCarrier rightCarrier
  constructor
  · intro classified
    have unrotatedClassified :
        (let Carrier : BHist -> Prop := UnaryHistory
         let Classifier : BHist -> BHist -> Prop :=
          fun x y => Carrier x ∧ Carrier y ∧ hsame x y
         Classifier (append left (append middle right))
          (append left (append middle' right))) := by
      dsimp
      have rightCarrier' : UnaryHistory (append left (append middle' right)) := by
        exact (append_assoc left middle' right) ▸ classified.right.left
      have sameRight :
          hsame (append left (append middle right)) (append left (append middle' right)) := by
        exact (append_assoc left middle' right) ▸ classified.right.right
      exact And.intro classified.left (And.intro rightCarrier' sameRight)
    exact Iff.mp
      (concrete_unary_history_magma_classifier_append_middle_cancel_iff
        (left := left) (middle := middle) (middle' := middle') (right := right)
        leftCarrier rightCarrier)
      unrotatedClassified
  · intro core
    have unrotatedClassified :=
      Iff.mpr
        (concrete_unary_history_magma_classifier_append_middle_cancel_iff
          (left := left) (middle := middle) (middle' := middle') (right := right)
          leftCarrier rightCarrier)
        core
    have rotatedCarrier : UnaryHistory (append (append left middle') right) := by
      exact Eq.symm (append_assoc left middle' right) ▸ unrotatedClassified.right.left
    have sameRotated :
        hsame (append left (append middle right)) (append (append left middle') right) := by
      exact Eq.symm (append_assoc left middle' right) ▸ unrotatedClassified.right.right
    exact And.intro unrotatedClassified.left (And.intro rotatedCarrier sameRotated)

theorem concrete_unary_history_magma_cont_common_context_classifier_iff
    {left left' middle middle' right right' r r' : BHist} :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
    Classifier left left' -> Classifier right right' ->
      Cont left (append middle right) r ->
        Cont left' (append middle' right') r' ->
          (Classifier r r' ↔ Carrier middle ∧ Carrier middle' ∧ hsame middle middle') := by
  dsimp
  intro leftClassified rightClassified leftCont rightCont
  cases leftClassified.right.right
  cases rightClassified.right.right
  cases leftCont
  cases rightCont
  exact concrete_unary_history_magma_classifier_append_middle_cancel_iff
    leftClassified.left rightClassified.left

theorem concrete_unary_history_magma_cont_nested_common_context_classifier_iff
    {left left' middle middle' right right' lm lm' out out' : BHist} :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
    Classifier left left' -> Classifier right right' ->
      Cont left middle lm -> Cont lm right out ->
        Cont left' middle' lm' -> Cont lm' right' out' ->
          (Classifier out out' ↔ Carrier middle ∧ Carrier middle' ∧ hsame middle middle') := by
  dsimp
  intro leftClassified rightClassified leftMiddle leftResult rightMiddle rightResult
  cases leftClassified.right.right
  cases rightClassified.right.right
  cases leftMiddle
  cases leftResult
  cases rightMiddle
  cases rightResult
  constructor
  · intro classified
    have nestedClassified :
        (let Carrier : BHist -> Prop := UnaryHistory
         let Classifier : BHist -> BHist -> Prop :=
          fun x y => Carrier x ∧ Carrier y ∧ hsame x y
         Classifier (append left (append middle right))
          (append left (append middle' right))) := by
      dsimp
      have leftNestedCarrier : UnaryHistory (append left (append middle right)) :=
        append_assoc left middle right ▸ classified.left
      have rightNestedCarrier : UnaryHistory (append left (append middle' right)) :=
        append_assoc left middle' right ▸ classified.right.left
      have sameLeftNested :
          hsame (append left (append middle right)) (append (append left middle') right) :=
        append_assoc left middle right ▸ classified.right.right
      have sameNested :
          hsame (append left (append middle right)) (append left (append middle' right)) :=
        append_assoc left middle' right ▸ sameLeftNested
      exact And.intro leftNestedCarrier (And.intro rightNestedCarrier sameNested)
    exact Iff.mp
      (concrete_unary_history_magma_classifier_append_middle_cancel_iff
        (left := left) (middle := middle) (middle' := middle') (right := right)
        leftClassified.left rightClassified.left)
      nestedClassified
  · intro core
    have nestedClassified :=
      Iff.mpr
        (concrete_unary_history_magma_classifier_append_middle_cancel_iff
          (left := left) (middle := middle) (middle' := middle') (right := right)
          leftClassified.left rightClassified.left)
        core
    have leftCarrier : UnaryHistory (append (append left middle) right) :=
      Eq.symm (append_assoc left middle right) ▸ nestedClassified.left
    have rightCarrier : UnaryHistory (append (append left middle') right) :=
      Eq.symm (append_assoc left middle' right) ▸ nestedClassified.right.left
    have sameLeftAssociated :
        hsame (append (append left middle) right) (append left (append middle' right)) :=
      Eq.symm (append_assoc left middle right) ▸ nestedClassified.right.right
    have sameAssociated :
        hsame (append (append left middle) right) (append (append left middle') right) :=
      Eq.symm (append_assoc left middle' right) ▸ sameLeftAssociated
    exact And.intro leftCarrier (And.intro rightCarrier sameAssociated)

end BEDC.Derived.MagmaUp
