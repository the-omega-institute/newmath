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

theorem concrete_unary_history_magma_cont_visible_right_result_nonempty {h t r : BHist} :
    (Cont h (BHist.e0 t) r -> hsame r BHist.Empty -> False) ∧
      (Cont h (BHist.e1 t) r -> hsame r BHist.Empty -> False) := by
  constructor
  · intro continuation resultEmpty
    have emptyContinuation : Cont h (BHist.e0 t) BHist.Empty :=
      cont_result_hsame_transport continuation resultEmpty
    exact not_hsame_e0_empty (cont_empty_result_inversion emptyContinuation).right
  · intro continuation resultEmpty
    have emptyContinuation : Cont h (BHist.e1 t) BHist.Empty :=
      cont_result_hsame_transport continuation resultEmpty
    exact not_hsame_e1_empty (cont_empty_result_inversion emptyContinuation).right

theorem concrete_unary_history_magma_cont_visible_left_result_nonempty {h t r : BHist} :
    (Cont (BHist.e0 t) h r -> hsame r BHist.Empty -> False) ∧
      (Cont (BHist.e1 t) h r -> hsame r BHist.Empty -> False) := by
  constructor
  · intro continuation resultEmpty
    have emptyContinuation : Cont (BHist.e0 t) h BHist.Empty :=
      cont_result_hsame_transport continuation resultEmpty
    exact not_hsame_e0_empty (cont_empty_result_inversion emptyContinuation).left
  · intro continuation resultEmpty
    have emptyContinuation : Cont (BHist.e1 t) h BHist.Empty :=
      cont_result_hsame_transport continuation resultEmpty
    exact not_hsame_e1_empty (cont_empty_result_inversion emptyContinuation).left

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

theorem concrete_unary_history_magma_cont_left_context_classifier_iff
    {left left' right right' out out' : BHist} :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
    Classifier left left' -> Cont left right out -> Cont left' right' out' ->
      (Classifier out out' ↔ Carrier right ∧ Carrier right' ∧ hsame right right') := by
  dsimp
  intro leftClassified leftCont rightCont
  constructor
  · intro outClassified
    have rightCarrier : UnaryHistory right :=
      (Iff.mp (concrete_unary_history_magma_cont_result_unary_iff leftCont)
        outClassified.left).right
    have rightCarrier' : UnaryHistory right' :=
      (Iff.mp (concrete_unary_history_magma_cont_result_unary_iff rightCont)
        outClassified.right.left).right
    have sameRight : hsame right right' := by
      cases leftClassified.right.right
      cases leftCont
      cases rightCont
      exact append_left_cancel outClassified.right.right
    exact And.intro rightCarrier (And.intro rightCarrier' sameRight)
  · intro rightData
    have outCarrier : UnaryHistory out :=
      unary_cont_closed leftClassified.left rightData.left leftCont
    have outCarrier' : UnaryHistory out' :=
      unary_cont_closed leftClassified.right.left rightData.right.left rightCont
    have sameOut : hsame out out' :=
      cont_respects_hsame leftClassified.right.right rightData.right.right leftCont rightCont
    exact And.intro outCarrier (And.intro outCarrier' sameOut)

theorem concrete_unary_history_magma_cont_left_unit_classifier_iff {h k r : BHist} :
    Cont h k r ->
      (let Carrier : BHist -> Prop := UnaryHistory
       let Classifier : BHist -> BHist -> Prop :=
        fun x y => Carrier x ∧ Carrier y ∧ hsame x y
       Classifier r k ↔ Carrier k ∧ hsame h BHist.Empty) := by
  intro rel
  dsimp
  constructor
  · intro classified
    have leftUnitContinuation : Cont h k k :=
      cont_result_hsame_transport rel classified.right.right
    exact And.intro classified.right.left (cont_left_unit_unique leftUnitContinuation)
  · intro data
    have leftCarrier : UnaryHistory h := by
      cases data.right
      exact unary_empty
    have resultCarrier : UnaryHistory r :=
      unary_cont_closed leftCarrier data.left rel
    have sameResult : hsame r k := by
      cases data.right
      exact (cont_left_unit_iff (h := k) (r := r)).mp rel
    exact And.intro resultCarrier (And.intro data.left sameResult)

theorem concrete_unary_history_magma_cont_right_unit_classifier_iff {h k r : BHist} :
    Cont h k r ->
      (let Carrier : BHist -> Prop := UnaryHistory
       let Classifier : BHist -> BHist -> Prop :=
        fun x y => Carrier x ∧ Carrier y ∧ hsame x y
       Classifier r h ↔ Carrier h ∧ hsame k BHist.Empty) := by
  intro rel
  dsimp
  constructor
  · intro classified
    have rightUnitContinuation : Cont h k h :=
      cont_result_hsame_transport rel classified.right.right
    exact And.intro classified.right.left (cont_right_unit_unique rightUnitContinuation)
  · intro data
    have rightCarrier : UnaryHistory k := by
      cases data.right
      exact unary_empty
    have resultCarrier : UnaryHistory r :=
      unary_cont_closed data.left rightCarrier rel
    have sameResult : hsame r h := by
      cases data.right
      exact (cont_right_unit_iff (h := h) (r := r)).mp rel
    exact And.intro resultCarrier (And.intro data.left sameResult)

theorem concrete_unary_history_magma_cont_result_both_inputs_classifier_empty_iff {h k r : BHist} :
    Cont h k r ->
      (let Carrier : BHist -> Prop := UnaryHistory
       let Classifier : BHist -> BHist -> Prop :=
        fun x y => Carrier x ∧ Carrier y ∧ hsame x y
       (Classifier r h ∧ Classifier r k) ↔
        Carrier h ∧ Carrier k ∧ hsame h BHist.Empty ∧ hsame k BHist.Empty) := by
  intro rel
  dsimp
  constructor
  · intro classified
    have rightUnitData :=
      Iff.mp (concrete_unary_history_magma_cont_right_unit_classifier_iff rel)
        classified.left
    have leftUnitData :=
      Iff.mp (concrete_unary_history_magma_cont_left_unit_classifier_iff rel)
        classified.right
    exact And.intro rightUnitData.left
      (And.intro leftUnitData.left (And.intro leftUnitData.right rightUnitData.right))
  · intro data
    constructor
    · exact Iff.mpr (concrete_unary_history_magma_cont_right_unit_classifier_iff rel)
        (And.intro data.left data.right.right.right)
    · exact Iff.mpr (concrete_unary_history_magma_cont_left_unit_classifier_iff rel)
        (And.intro data.right.left data.right.right.left)

theorem concrete_unary_history_magma_cont_right_context_classifier_iff
    {left left' right right' out out' : BHist} :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun x y => Carrier x ∧ Carrier y ∧ hsame x y
    Classifier right right' -> Cont left right out -> Cont left' right' out' ->
      (Classifier out out' ↔ Carrier left ∧ Carrier left' ∧ hsame left left') := by
  dsimp
  intro rightClassified leftCont rightCont
  constructor
  · intro outClassified
    have leftCarrier : UnaryHistory left :=
      (Iff.mp (concrete_unary_history_magma_cont_result_unary_iff leftCont)
        outClassified.left).left
    have leftCarrier' : UnaryHistory left' :=
      (Iff.mp (concrete_unary_history_magma_cont_result_unary_iff rightCont)
        outClassified.right.left).left
    have sameLeft : hsame left left' := by
      cases rightClassified.right.right
      cases leftCont
      cases rightCont
      exact append_right_cancel (k := right) outClassified.right.right
    exact And.intro leftCarrier (And.intro leftCarrier' sameLeft)
  · intro leftData
    have outCarrier : UnaryHistory out :=
      unary_cont_closed leftData.left rightClassified.left leftCont
    have outCarrier' : UnaryHistory out' :=
      unary_cont_closed leftData.right.left rightClassified.right.left rightCont
    have sameOut : hsame out out' :=
      cont_respects_hsame leftData.right.right rightClassified.right.right leftCont rightCont
    exact And.intro outCarrier (And.intro outCarrier' sameOut)

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

theorem concrete_unary_history_magma_cont_nested_left_unit_classifier_iff
    {left middle right lm out : BHist} :
    Cont left middle lm -> Cont lm right out ->
      (let Carrier : BHist -> Prop := UnaryHistory
       let Classifier : BHist -> BHist -> Prop :=
        fun x y => Carrier x ∧ Carrier y ∧ hsame x y
       Classifier out right ↔
        Carrier right ∧ hsame left BHist.Empty ∧ hsame middle BHist.Empty) := by
  intro leftMiddle leftResult
  dsimp
  constructor
  · intro classified
    have leftUnitData :=
      Iff.mp
        (concrete_unary_history_magma_cont_left_unit_classifier_iff leftResult)
        classified
    have emptyFactors : hsame left BHist.Empty ∧ hsame middle BHist.Empty := by
      cases leftMiddle
      exact append_eq_empty_iff.mp leftUnitData.right
    exact And.intro leftUnitData.left emptyFactors
  · intro data
    have leftMiddleEmpty : hsame lm BHist.Empty := by
      cases leftMiddle
      exact append_eq_empty_iff.mpr (And.intro data.right.left data.right.right)
    exact
      Iff.mpr
        (concrete_unary_history_magma_cont_left_unit_classifier_iff leftResult)
        (And.intro data.left leftMiddleEmpty)

theorem concrete_unary_history_magma_cont_nested_right_unit_classifier_iff
    {left middle right lm out : BHist} :
    Cont left middle lm -> Cont lm right out ->
      (let Carrier : BHist -> Prop := UnaryHistory
       let Classifier : BHist -> BHist -> Prop :=
        fun x y => Carrier x ∧ Carrier y ∧ hsame x y
       Classifier out left ↔
        Carrier left ∧ hsame middle BHist.Empty ∧ hsame right BHist.Empty) := by
  intro leftMiddle leftResult
  dsimp
  constructor
  · intro classified
    have middleRight : Cont middle right (append middle right) := by
      rfl
    have leftMiddleRight : Cont left (append middle right) out := by
      have same :=
        cont_assoc_relational leftMiddle leftResult middleRight
          (cont_intro (h := left) (k := append middle right) (r := append left (append middle right))
            rfl)
      exact cont_result_hsame_transport
        (cont_intro (h := left) (k := append middle right)
          (r := append left (append middle right)) rfl)
        (hsame_symm same)
    have rightEmpty : hsame (append middle right) BHist.Empty :=
      cont_right_unit_unique
        (cont_result_hsame_transport leftMiddleRight classified.right.right)
    have emptyFactors := append_eq_empty_iff.mp rightEmpty
    exact And.intro classified.right.left
      (And.intro emptyFactors.left emptyFactors.right)
  · intro data
    have middleCarrier : UnaryHistory middle := by
      cases data.right.left
      exact unary_empty
    have lmCarrier : UnaryHistory lm :=
      unary_cont_closed data.left middleCarrier leftMiddle
    have sameLmLeft : hsame lm left := by
      cases data.right.left
      exact (cont_right_unit_iff (h := left) (r := lm)).mp leftMiddle
    have outLmClassified :=
      Iff.mpr
        (concrete_unary_history_magma_cont_right_unit_classifier_iff leftResult)
        (And.intro lmCarrier data.right.right)
    exact And.intro outLmClassified.left
      (And.intro data.left (hsame_trans outLmClassified.right.right sameLmLeft))

theorem MagmaUp_StdBridge :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    SemanticNameCert Carrier Carrier Carrier Classifier ∧
      (forall {h k : BHist}, Carrier h -> Carrier k ->
        Carrier (append h k) ∧ Cont h k (append h k)) ∧
      (forall {h t r : BHist}, Cont h (BHist.e0 t) r ->
        hsame r BHist.Empty -> False) ∧
      (forall {h t r : BHist}, Cont h (BHist.e1 t) r ->
        hsame r BHist.Empty -> False) := by
  exact And.intro
    ConcreteUnaryHistoryMagma_semanticNameCert.left
    (And.intro
      ConcreteUnaryHistoryMagma_semanticNameCert.right.left
      (And.intro
        (fun {h t r : BHist} =>
          concrete_unary_history_magma_cont_visible_right_result_nonempty
            (h := h) (t := t) (r := r) |>.left)
        (fun {h t r : BHist} =>
          concrete_unary_history_magma_cont_visible_right_result_nonempty
            (h := h) (t := t) (r := r) |>.right)))

end BEDC.Derived.MagmaUp
