import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Derived.IntUp.CommRing
namespace BEDC.Derived.MatrixUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
def MatrixSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty
def MatrixSingletonClassifier (h k : BHist) : Prop :=
  MatrixSingletonCarrier h ∧ MatrixSingletonCarrier k ∧ hsame h k
def MatrixSingletonZero : BHist :=
  BHist.Empty
def MatrixSingletonOne : BHist :=
  BHist.Empty
def MatrixSingletonAdd (M N : BHist) : BHist :=
  append M N
def MatrixSingletonMul (M N : BHist) : BHist :=
  append M N
def MatrixSingletonPow (M exponent : BHist) : BHist :=
  match exponent with
  | BHist.Empty => MatrixSingletonOne
  | BHist.e0 _ => MatrixSingletonZero
  | BHist.e1 tail => MatrixSingletonMul (MatrixSingletonPow M tail) M
theorem MatrixSingletonPow_carrier_closed {M exponent : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory exponent ->
      MatrixSingletonCarrier (MatrixSingletonPow M exponent) := by
  intro carrierM exponentUnary
  induction exponent with
  | Empty =>
      exact hsame_refl BHist.Empty
  | e0 tail _ih =>
      exact hsame_refl BHist.Empty
  | e1 tail ih =>
      exact append_eq_empty_iff.mpr (And.intro (ih exponentUnary) carrierM)
theorem MatrixSingletonPow_carrier_nonempty_unary_input_iff {M exponent : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      (MatrixSingletonCarrier (MatrixSingletonPow M exponent) ↔ MatrixSingletonCarrier M) := by
  intro exponentUnary exponentNonempty
  constructor
  · intro powCarrier
    cases exponent with
    | Empty =>
        exact False.elim (exponentNonempty (hsame_refl BHist.Empty))
    | e0 tail =>
        cases exponentUnary
    | e1 tail =>
        exact (append_eq_empty_iff.mp powCarrier).right
  · intro carrierM
    exact MatrixSingletonPow_carrier_closed carrierM exponentUnary
theorem MatrixSingletonPow_nonempty_unary_suffix_base_carrier {M e tail : BHist} :
    UnaryHistory tail -> (hsame tail BHist.Empty -> False) ->
      MatrixSingletonCarrier (MatrixSingletonPow M (append e tail)) ->
        MatrixSingletonCarrier M := by
  intro tailUnary tailNonempty powCarrier
  cases tail with
  | Empty =>
      exact False.elim (tailNonempty (hsame_refl BHist.Empty))
  | e0 tail =>
      cases tailUnary
  | e1 tail =>
      exact (append_eq_empty_iff.mp powCarrier).right
theorem MatrixSingletonPow_positive_exponent_cont_readback {M exponent : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      ∃ tail : BHist, UnaryHistory tail ∧
        Cont (MatrixSingletonPow M tail) M (MatrixSingletonPow M exponent) := by
  intro exponentUnary exponentNonempty
  have exponentTail := unary_history_nonempty_e1_tail exponentUnary exponentNonempty
  cases exponentTail with
  | intro tail data =>
      cases data.left
      exact ⟨tail, data.right, cont_intro rfl⟩
theorem MatrixSingletonPow_succ_classifier {M exponent : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory exponent ->
      MatrixSingletonClassifier (MatrixSingletonPow M (BHist.e1 exponent))
        (MatrixSingletonMul (MatrixSingletonPow M exponent) M) := by
  intro carrierM exponentUnary
  have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M exponent) :=
    MatrixSingletonPow_carrier_closed carrierM exponentUnary
  have resultCarrier : MatrixSingletonCarrier
      (MatrixSingletonMul (MatrixSingletonPow M exponent) M) :=
    append_eq_empty_iff.mpr (And.intro powCarrier carrierM)
  exact And.intro resultCarrier
    (And.intro resultCarrier (hsame_refl (MatrixSingletonMul (MatrixSingletonPow M exponent) M)))
theorem MatrixSingletonPow_succ_endpoint_exactness {M exponent : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory exponent ->
      MatrixSingletonCarrier (MatrixSingletonPow M (BHist.e1 exponent)) ∧ MatrixSingletonClassifier
        (MatrixSingletonPow M (BHist.e1 exponent)) (MatrixSingletonMul (MatrixSingletonPow M exponent) M) ∧
          MatrixSingletonClassifier (MatrixSingletonPow M (BHist.e1 exponent)) (MatrixSingletonMul M (MatrixSingletonPow M exponent)) := by
  intro carrierM exponentUnary
  have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M exponent) :=
    MatrixSingletonPow_carrier_closed carrierM exponentUnary
  have firstClassified :
      MatrixSingletonClassifier (MatrixSingletonPow M (BHist.e1 exponent))
        (MatrixSingletonMul (MatrixSingletonPow M exponent) M) :=
    MatrixSingletonPow_succ_classifier carrierM exponentUnary
  have reversedCarrier :
      MatrixSingletonCarrier (MatrixSingletonMul M (MatrixSingletonPow M exponent)) :=
    append_eq_empty_iff.mpr (And.intro carrierM powCarrier)
  have reversedSame :
      hsame (MatrixSingletonPow M (BHist.e1 exponent))
        (MatrixSingletonMul M (MatrixSingletonPow M exponent)) :=
    hsame_trans firstClassified.left (hsame_symm reversedCarrier)
  exact ⟨firstClassified.left, firstClassified, firstClassified.left, reversedCarrier, reversedSame⟩
theorem MatrixSingletonPow_successor_endpoint_exactness {M exponent : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory exponent ->
      MatrixSingletonCarrier (MatrixSingletonPow M (BHist.e1 exponent)) ∧
        MatrixSingletonClassifier (MatrixSingletonPow M (BHist.e1 exponent)) (MatrixSingletonMul (MatrixSingletonPow M exponent) M) ∧
        MatrixSingletonClassifier (MatrixSingletonPow M (BHist.e1 exponent)) (MatrixSingletonMul M (MatrixSingletonPow M exponent)) := by
  exact MatrixSingletonPow_succ_endpoint_exactness
theorem MatrixSingletonPow_succ_continuation_classifier {M exponent r : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory exponent ->
      Cont (MatrixSingletonPow M exponent) M r ->
        MatrixSingletonClassifier (MatrixSingletonPow M (BHist.e1 exponent)) r := by
  intro carrierM exponentUnary continuation
  have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M exponent) :=
    MatrixSingletonPow_carrier_closed carrierM exponentUnary
  have succCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (BHist.e1 exponent)) :=
    append_eq_empty_iff.mpr (And.intro powCarrier carrierM)
  have resultCarrier : MatrixSingletonCarrier r := by
    cases continuation
    exact succCarrier
  have sameResult : hsame (MatrixSingletonPow M (BHist.e1 exponent)) r := by
    cases continuation
    rfl
  exact And.intro succCarrier (And.intro resultCarrier sameResult)
theorem MatrixSingletonPow_visible_base_succ_continuation_empty_result_absurd
    {m exponent y r : BHist} :
    MatrixSingletonCarrier y ->
      (Cont (MatrixSingletonPow (BHist.e0 m) (BHist.e1 exponent)) y r ->
        hsame r BHist.Empty -> False) ∧
      (Cont (MatrixSingletonPow (BHist.e1 m) (BHist.e1 exponent)) y r ->
        hsame r BHist.Empty -> False) := by
  intro _carrierY
  constructor
  · intro continuation resultEmpty
    have sourceParts := append_eq_empty_iff.mp
      (cont_empty_result_inversion (cont_result_hsame_transport continuation resultEmpty)).left
    exact not_hsame_e0_empty sourceParts.right
  · intro continuation resultEmpty
    have sourceParts := append_eq_empty_iff.mp
      (cont_empty_result_inversion (cont_result_hsame_transport continuation resultEmpty)).left
    exact not_hsame_e1_empty sourceParts.right

theorem MatrixSingletonPow_positive_exponent_visible_base_continuation_empty_result_absurd {m exponent y r : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) ->
      (Cont (MatrixSingletonPow (BHist.e0 m) exponent) y r -> hsame r BHist.Empty -> False) ∧
      (Cont (MatrixSingletonPow (BHist.e1 m) exponent) y r -> hsame r BHist.Empty -> False) := by
  intro exponentUnary exponentNonempty
  exact And.intro
    (fun continuation resultEmpty => not_hsame_e0_empty
      ((MatrixSingletonPow_carrier_nonempty_unary_input_iff exponentUnary exponentNonempty).mp
        (cont_empty_result_inversion (cont_result_hsame_transport continuation resultEmpty)).left))
    (fun continuation resultEmpty => not_hsame_e1_empty
      ((MatrixSingletonPow_carrier_nonempty_unary_input_iff exponentUnary exponentNonempty).mp
        (cont_empty_result_inversion (cont_result_hsame_transport continuation resultEmpty)).left))
theorem MatrixSingletonPow_nonempty_base_continuation_result_absurd {M exponent y r : BHist} :
    UnaryHistory exponent -> (hsame exponent BHist.Empty -> False) -> (MatrixSingletonCarrier M -> False) -> Cont (MatrixSingletonPow M exponent) y r -> hsame r BHist.Empty -> False := by
  intro exponentUnary exponentNonempty baseNonempty continuation resultEmpty
  have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M exponent) :=
    (cont_empty_result_inversion (cont_result_hsame_transport continuation resultEmpty)).left
  exact baseNonempty ((MatrixSingletonPow_carrier_nonempty_unary_input_iff exponentUnary exponentNonempty).mp powCarrier)
theorem MatrixSingletonPow_append_exponent_classifier {M w q : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory w -> UnaryHistory q ->
      MatrixSingletonClassifier (MatrixSingletonPow M (append w q)) (MatrixSingletonMul (MatrixSingletonPow M w) (MatrixSingletonPow M q)) := by
  intro carrierM unaryW unaryQ
  have compositeCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (append w q)) :=
    MatrixSingletonPow_carrier_closed carrierM (unary_append_closed unaryW unaryQ)
  have leftCarrier : MatrixSingletonCarrier (MatrixSingletonPow M w) :=
    MatrixSingletonPow_carrier_closed carrierM unaryW
  have rightCarrier : MatrixSingletonCarrier (MatrixSingletonPow M q) :=
    MatrixSingletonPow_carrier_closed carrierM unaryQ
  have productCarrier :
      MatrixSingletonCarrier
        (MatrixSingletonMul (MatrixSingletonPow M w) (MatrixSingletonPow M q)) :=
    append_eq_empty_iff.mpr (And.intro leftCarrier rightCarrier)
  exact And.intro compositeCarrier
    (And.intro productCarrier (hsame_trans compositeCarrier (hsame_symm productCarrier)))
theorem MatrixSingletonPow_append_succ_right_exponent_classifier {M w q : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory w -> UnaryHistory q -> MatrixSingletonClassifier
      (MatrixSingletonPow M (append w (BHist.e1 q))) (MatrixSingletonMul (MatrixSingletonPow M w) (MatrixSingletonMul (MatrixSingletonPow M q) M)) := by
  intro carrierM unaryW unaryQ
  have compositeCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (append w (BHist.e1 q))) :=
    MatrixSingletonPow_carrier_closed carrierM (unary_append_closed unaryW (unary_e1_closed unaryQ))
  have leftCarrier : MatrixSingletonCarrier (MatrixSingletonPow M w) :=
    MatrixSingletonPow_carrier_closed carrierM unaryW
  have rightPowCarrier : MatrixSingletonCarrier (MatrixSingletonPow M q) :=
    MatrixSingletonPow_carrier_closed carrierM unaryQ
  have rightMulCarrier : MatrixSingletonCarrier (MatrixSingletonMul (MatrixSingletonPow M q) M) :=
    append_eq_empty_iff.mpr (And.intro rightPowCarrier carrierM)
  have productCarrier : MatrixSingletonCarrier
      (MatrixSingletonMul (MatrixSingletonPow M w)
        (MatrixSingletonMul (MatrixSingletonPow M q) M)) :=
    append_eq_empty_iff.mpr (And.intro leftCarrier rightMulCarrier)
  exact And.intro compositeCarrier
    (And.intro productCarrier (hsame_trans compositeCarrier (hsame_symm productCarrier)))
theorem MatrixSingletonPow_append_exponent_comm_classifier {M w q : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory w -> UnaryHistory q ->
      MatrixSingletonClassifier (MatrixSingletonPow M (append w q)) (MatrixSingletonPow M (append q w)) := by
  intro carrierM unaryW unaryQ
  have leftCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (append w q)) :=
    MatrixSingletonPow_carrier_closed carrierM (unary_append_closed unaryW unaryQ)
  have rightCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (append q w)) :=
    MatrixSingletonPow_carrier_closed carrierM (unary_append_closed unaryQ unaryW)
  exact And.intro leftCarrier
    (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
theorem MatrixSingletonPow_append_exponent_classifier_iff {M a b h : BHist} :
    MatrixSingletonCarrier M -> UnaryHistory a -> UnaryHistory b ->
      (MatrixSingletonClassifier (MatrixSingletonPow M (append a b)) h ↔
        MatrixSingletonCarrier h) := by
  intro carrierM unaryA unaryB
  have powCarrier : MatrixSingletonCarrier (MatrixSingletonPow M (append a b)) :=
    MatrixSingletonPow_carrier_closed carrierM (unary_append_closed unaryA unaryB)
  constructor
  · intro classified
    exact classified.right.left
  · intro carrierH
    exact And.intro powCarrier
      (And.intro carrierH (hsame_trans powCarrier (hsame_symm carrierH)))
theorem MatrixSingletonClassifier_append_split_empty_iff {M N h : BHist} :
    MatrixSingletonClassifier (append M N) h ↔
      hsame M BHist.Empty ∧ hsame N BHist.Empty ∧ MatrixSingletonCarrier h := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    exact And.intro emptyParts.left (And.intro emptyParts.right classified.right.left)
  · intro split
    have appendEmpty : hsame (append M N) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro split.left split.right.left)
    exact And.intro appendEmpty
      (And.intro split.right.right (hsame_trans appendEmpty (hsame_symm split.right.right)))

theorem MatrixSingletonClassifier_append_visible_right_absurd {h p q : BHist} :
    (MatrixSingletonClassifier h (append p (BHist.e0 q)) -> False) ∧
      (MatrixSingletonClassifier h (append p (BHist.e1 q)) -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.right.left
    cases emptyParts.right
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.right.left
    cases emptyParts.right

theorem MatrixSingletonClassifier_append_pair_carrier_iff {M N P Q : BHist} :
    MatrixSingletonClassifier (append M N) (append P Q) ↔
      MatrixSingletonCarrier M ∧ MatrixSingletonCarrier N ∧
        MatrixSingletonCarrier P ∧ MatrixSingletonCarrier Q := by
  constructor
  · intro classified
    have leftParts := append_eq_empty_iff.mp classified.left
    have rightParts := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftParts.left
      (And.intro leftParts.right (And.intro rightParts.left rightParts.right))
  · intro carriers
    have leftEmpty : hsame (append M N) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro carriers.left carriers.right.left)
    have rightEmpty : hsame (append P Q) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro carriers.right.right.left carriers.right.right.right)
    exact And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem MatrixSingletonClassifier_append_self_context_split_iff {a x b : BHist} :
    MatrixSingletonClassifier (append a (append x a)) b <->
      MatrixSingletonCarrier a ∧ MatrixSingletonClassifier x b := by
  constructor
  · intro classified
    have outerSplit := append_eq_empty_iff.mp classified.left
    have innerSplit := append_eq_empty_iff.mp outerSplit.right
    have middleClassified : MatrixSingletonClassifier x b :=
      And.intro innerSplit.left
        (And.intro classified.right.left
          (hsame_trans innerSplit.left (hsame_symm classified.right.left)))
    exact And.intro outerSplit.left middleClassified
  · intro split
    have innerCarrier : MatrixSingletonCarrier (append x a) :=
      append_eq_empty_iff.mpr (And.intro split.right.left split.left)
    have leftCarrier : MatrixSingletonCarrier (append a (append x a)) :=
      append_eq_empty_iff.mpr (And.intro split.left innerCarrier)
    exact And.intro leftCarrier
      (And.intro split.right.right.left
        (hsame_trans leftCarrier (hsame_symm split.right.right.left)))

theorem MatrixSingletonClassifier_append_right_cancel_iff {P Q R : BHist} :
    MatrixSingletonClassifier (append P R) (append Q R) <->
      MatrixSingletonClassifier P Q ∧ MatrixSingletonCarrier R := by
  constructor
  · intro classified
    have leftParts := append_eq_empty_iff.mp classified.left
    have rightParts := append_eq_empty_iff.mp classified.right.left
    have baseClassified : MatrixSingletonClassifier P Q :=
      And.intro leftParts.left
        (And.intro rightParts.left (hsame_trans leftParts.left (hsame_symm rightParts.left)))
    exact And.intro baseClassified leftParts.right
  · intro data
    have carrierP : MatrixSingletonCarrier P := data.left.left
    have carrierQ : MatrixSingletonCarrier Q := data.left.right.left
    have carrierR : MatrixSingletonCarrier R := data.right
    cases carrierP
    cases carrierQ
    cases carrierR
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem MatrixSingletonClassifier_append_common_context_iff {L P Q R : BHist} :
    MatrixSingletonClassifier (append L (append P R)) (append L (append Q R)) <->
      MatrixSingletonCarrier L ∧ MatrixSingletonClassifier P Q ∧ MatrixSingletonCarrier R := by
  constructor
  · intro classified
    have leftParts := append_eq_empty_iff.mp classified.left
    have leftMiddleParts := append_eq_empty_iff.mp leftParts.right
    have rightParts := append_eq_empty_iff.mp classified.right.left
    have rightMiddleParts := append_eq_empty_iff.mp rightParts.right
    have middleClassified : MatrixSingletonClassifier P Q :=
      And.intro leftMiddleParts.left
        (And.intro rightMiddleParts.left
          (hsame_trans leftMiddleParts.left (hsame_symm rightMiddleParts.left)))
    exact And.intro leftParts.left (And.intro middleClassified leftMiddleParts.right)
  · intro data
    have leftEmpty : hsame (append L (append P R)) BHist.Empty :=
      append_eq_empty_iff.mpr
        (And.intro data.left
          (append_eq_empty_iff.mpr (And.intro data.right.left.left data.right.right)))
    have rightEmpty : hsame (append L (append Q R)) BHist.Empty :=
      append_eq_empty_iff.mpr
        (And.intro data.left
          (append_eq_empty_iff.mpr (And.intro data.right.left.right.left data.right.right)))
    exact And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem MatrixSingletonClassifier_append_left_cancel_iff {P Q R : BHist} :
    MatrixSingletonClassifier (append R P) (append R Q) ↔
      MatrixSingletonCarrier R ∧ MatrixSingletonClassifier P Q := by
  constructor
  · intro classified
    have leftParts := append_eq_empty_iff.mp classified.left
    have rightParts := append_eq_empty_iff.mp classified.right.left
    have baseClassified : MatrixSingletonClassifier P Q :=
      And.intro leftParts.right
        (And.intro rightParts.right (hsame_trans leftParts.right (hsame_symm rightParts.right)))
    exact And.intro leftParts.left baseClassified
  · intro data
    have carrierR : MatrixSingletonCarrier R := data.left
    have classifiedPQ : MatrixSingletonClassifier P Q := data.right
    have leftEmpty : hsame (append R P) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro carrierR classifiedPQ.left)
    have rightEmpty : hsame (append R Q) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro carrierR classifiedPQ.right.left)
    exact And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem MatrixSingletonEmptyHistory_laws :
    SemanticNameCert MatrixSingletonCarrier MatrixSingletonCarrier MatrixSingletonCarrier
        MatrixSingletonClassifier ∧
      MatrixSingletonCarrier MatrixSingletonZero ∧
      MatrixSingletonCarrier MatrixSingletonOne ∧
      (forall {M N : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        MatrixSingletonCarrier (MatrixSingletonAdd M N) ∧
          MatrixSingletonCarrier (MatrixSingletonMul M N)) ∧
      (forall {M : BHist}, MatrixSingletonCarrier M ->
        MatrixSingletonClassifier (MatrixSingletonAdd MatrixSingletonZero M) M ∧
          MatrixSingletonClassifier (MatrixSingletonAdd M MatrixSingletonZero) M) ∧
      (forall {M : BHist}, MatrixSingletonCarrier M ->
        MatrixSingletonClassifier (MatrixSingletonMul MatrixSingletonOne M) M ∧
          MatrixSingletonClassifier (MatrixSingletonMul M MatrixSingletonOne) M) ∧
      (forall {M N P : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        MatrixSingletonCarrier P ->
          MatrixSingletonClassifier (MatrixSingletonAdd (MatrixSingletonAdd M N) P)
            (MatrixSingletonAdd M (MatrixSingletonAdd N P)) ∧
          MatrixSingletonClassifier (MatrixSingletonMul (MatrixSingletonMul M N) P)
            (MatrixSingletonMul M (MatrixSingletonMul N P))) ∧
      (forall {M M' N N' : BHist}, MatrixSingletonClassifier M M' ->
        MatrixSingletonClassifier N N' ->
          MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonAdd M' N') ∧
          MatrixSingletonClassifier (MatrixSingletonMul M N) (MatrixSingletonMul M' N')) := by
  have emptyCarrier : MatrixSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : MatrixSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have appendCarrier :
      forall {M N : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        MatrixSingletonCarrier (append M N) := by
    intro M N carrierM carrierN
    cases carrierM
    cases carrierN
    exact hsame_refl BHist.Empty
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
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
            (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
        carrier_respects_equiv := by
          intro h k same _carrier
          exact same.right.left
      }
      pattern_sound := by
        intro _h carrier
        exact carrier
      ledger_sound := by
        intro _h carrier
        exact carrier
    }
  · constructor
    · exact emptyCarrier
    · constructor
      · exact emptyCarrier
      · constructor
        · intro M N carrierM carrierN
          exact And.intro (appendCarrier carrierM carrierN) (appendCarrier carrierM carrierN)
        · constructor
          · intro M carrierM
            cases carrierM
            exact And.intro emptyClassified emptyClassified
          · constructor
            · intro M carrierM
              cases carrierM
              exact And.intro emptyClassified emptyClassified
            · constructor
              · intro M N P carrierM carrierN carrierP
                cases carrierM
                cases carrierN
                cases carrierP
                exact And.intro emptyClassified emptyClassified
              · intro M M' N N' sameMM' sameNN'
                cases sameMM'.left
                cases sameMM'.right.left
                cases sameNN'.left
                cases sameNN'.right.left
                exact And.intro emptyClassified emptyClassified

theorem MatrixSingletonEmptyHistory_endpoint_exactness {M N : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
      MatrixSingletonClassifier M BHist.Empty ∧
        MatrixSingletonClassifier MatrixSingletonZero BHist.Empty ∧
          MatrixSingletonClassifier MatrixSingletonOne BHist.Empty ∧
            MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty ∧
              MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty := by
  intro carrierM carrierN
  have emptyCarrier : MatrixSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : MatrixSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have appendCarrier : MatrixSingletonCarrier (append M N) := by
    cases carrierM
    cases carrierN
    exact hsame_refl BHist.Empty
  have appendClassified : MatrixSingletonClassifier (append M N) BHist.Empty :=
    And.intro appendCarrier (And.intro emptyCarrier appendCarrier)
  constructor
  · exact And.intro carrierM (And.intro emptyCarrier carrierM)
  · constructor
    · exact emptyClassified
    · constructor
      · exact emptyClassified
      · exact And.intro appendClassified appendClassified

theorem MatrixSingletonEmptyHistory_endpoint_collapse {M N : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
      MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty ∧
        MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty ∧
          MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonMul M N) := by
  intro carrierM carrierN
  have endpointExact := MatrixSingletonEmptyHistory_endpoint_exactness carrierM carrierN
  have addClassified : MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty :=
    endpointExact.right.right.right.left
  have mulClassified : MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty :=
    endpointExact.right.right.right.right
  have addMulClassified :
      MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonMul M N) :=
    And.intro addClassified.left
      (And.intro mulClassified.left (hsame_refl (MatrixSingletonAdd M N)))
  exact And.intro addClassified (And.intro mulClassified addMulClassified)

theorem MatrixSingletonAddMul_classifier_iff {M N : BHist} :
    MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonMul M N) <->
      hsame M BHist.Empty ∧ hsame N BHist.Empty := by
  constructor
  · intro classified
    exact append_eq_empty_iff.mp classified.left
  · intro emptyParts
    have appendEmpty : MatrixSingletonCarrier (append M N) :=
      append_eq_empty_iff.mpr emptyParts
    exact And.intro appendEmpty
      (And.intro appendEmpty (hsame_refl (MatrixSingletonAdd M N)))

theorem MatrixSingletonAddMul_continuation_result_iff {M N R : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
      (Cont (MatrixSingletonAdd M N) (MatrixSingletonMul M N) R ↔
        MatrixSingletonCarrier R) := by
  intro carrierM carrierN
  constructor
  · intro continuation
    cases carrierM
    cases carrierN
    exact cont_deterministic continuation (cont_right_unit BHist.Empty)
  · intro carrierR
    cases carrierM
    cases carrierN
    cases carrierR
    exact cont_right_unit BHist.Empty

theorem MatrixSingletonCarrier_continuation_append_target_result_iff {M N h R : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N -> Cont h (append M N) R ->
      (MatrixSingletonCarrier R ↔ MatrixSingletonCarrier h) := by
  intro carrierM carrierN continuation
  constructor
  · intro resultCarrier
    exact (cont_empty_result_inversion
      (cont_result_hsame_transport continuation resultCarrier)).left
  · intro carrierH
    exact cont_respects_hsame carrierH (append_eq_empty_iff.mpr (And.intro carrierM carrierN))
      continuation (cont_right_unit BHist.Empty)

theorem MatrixSingletonAddMul_continuation_empty_result_factors_iff {M N R : BHist} :
    Cont (MatrixSingletonAdd M N) (MatrixSingletonMul M N) R ->
      (hsame R BHist.Empty ↔ hsame M BHist.Empty ∧ hsame N BHist.Empty) := by
  intro continuation
  constructor
  · intro resultEmpty
    have emptyContinuation :
        Cont (MatrixSingletonAdd M N) (MatrixSingletonMul M N) BHist.Empty := by
      cases resultEmpty
      exact continuation
    have emptyFactors := cont_empty_result_inversion emptyContinuation
    exact append_eq_empty_iff.mp emptyFactors.left
  · intro emptyParts
    cases emptyParts.left
    cases emptyParts.right
    exact cont_deterministic continuation (cont_right_unit BHist.Empty)

theorem MatrixSingletonAddMul_visible_left_continuation_result_nonempty {m N R : BHist} :
    (Cont (MatrixSingletonAdd (BHist.e0 m) N) (MatrixSingletonMul (BHist.e0 m) N) R ->
      hsame R BHist.Empty -> False) ∧
    (Cont (MatrixSingletonAdd (BHist.e1 m) N) (MatrixSingletonMul (BHist.e1 m) N) R ->
      hsame R BHist.Empty -> False) := by
  constructor
  · intro continuation resultEmpty
    have emptyFactors :=
      Iff.mp (MatrixSingletonAddMul_continuation_empty_result_factors_iff continuation)
        resultEmpty
    exact not_hsame_e0_empty emptyFactors.left
  · intro continuation resultEmpty
    have emptyFactors :=
      Iff.mp (MatrixSingletonAddMul_continuation_empty_result_factors_iff continuation)
        resultEmpty
    exact not_hsame_e1_empty emptyFactors.left

theorem MatrixSingletonClassifier_continuation_comm_closed {M N left right : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N -> Cont M N left -> Cont N M right ->
      MatrixSingletonCarrier left ∧ MatrixSingletonCarrier right ∧
        MatrixSingletonClassifier left right := by
  intro carrierM carrierN leftCont rightCont
  cases carrierM
  cases carrierN
  cases leftCont
  cases rightCont
  have emptyCarrier : MatrixSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact And.intro emptyCarrier
    (And.intro emptyCarrier
      (And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))))

theorem MatrixSingletonMul_right_distributes_over_add {A B C : BHist} :
    MatrixSingletonCarrier A -> MatrixSingletonCarrier B -> MatrixSingletonCarrier C ->
      MatrixSingletonClassifier (MatrixSingletonMul (MatrixSingletonAdd A B) C)
        (MatrixSingletonAdd (MatrixSingletonMul A C) (MatrixSingletonMul B C)) := by
  intro carrierA carrierB carrierC
  have leftCarrier : MatrixSingletonCarrier (MatrixSingletonMul (MatrixSingletonAdd A B) C) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierA carrierB)) carrierC)
  have rightCarrier :
      MatrixSingletonCarrier (MatrixSingletonAdd (MatrixSingletonMul A C)
        (MatrixSingletonMul B C)) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierA carrierC))
        (append_eq_empty_iff.mpr (And.intro carrierB carrierC)))
  exact And.intro leftCarrier
    (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
theorem MatrixSingletonCarrier_continuation_visible_result_absurd {M N r : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
      (Cont M N (BHist.e0 r) -> False) ∧ (Cont M N (BHist.e1 r) -> False) := by
  intro carrierM carrierN
  constructor
  · intro continuation
    cases carrierM
    cases carrierN
    cases continuation
  · intro continuation
    cases carrierM
    cases carrierN
    cases continuation

structure Mat2 where
  a00 : BEDC.Derived.PrimeUp.IntegerUp
  a01 : BEDC.Derived.PrimeUp.IntegerUp
  a10 : BEDC.Derived.PrimeUp.IntegerUp
  a11 : BEDC.Derived.PrimeUp.IntegerUp

def MatEq (A B : Mat2) : Prop :=
  BEDC.Derived.RationalUp.IntEq A.a00 B.a00 ∧
    BEDC.Derived.RationalUp.IntEq A.a01 B.a01 ∧
      BEDC.Derived.RationalUp.IntEq A.a10 B.a10 ∧
        BEDC.Derived.RationalUp.IntEq A.a11 B.a11

def matZero : Mat2 :=
  { a00 := BEDC.Derived.RationalUp.intZero
    a01 := BEDC.Derived.RationalUp.intZero
    a10 := BEDC.Derived.RationalUp.intZero
    a11 := BEDC.Derived.RationalUp.intZero }

def matOne : Mat2 :=
  { a00 := BEDC.Derived.RationalUp.intOne
    a01 := BEDC.Derived.RationalUp.intZero
    a10 := BEDC.Derived.RationalUp.intZero
    a11 := BEDC.Derived.RationalUp.intOne }

def matAdd (A B : Mat2) : Mat2 :=
  { a00 := BEDC.Derived.RationalUp.IntAdd A.a00 B.a00
    a01 := BEDC.Derived.RationalUp.IntAdd A.a01 B.a01
    a10 := BEDC.Derived.RationalUp.IntAdd A.a10 B.a10
    a11 := BEDC.Derived.RationalUp.IntAdd A.a11 B.a11 }

def matNeg (A : Mat2) : Mat2 :=
  { a00 := BEDC.Derived.RationalUp.IntNeg A.a00
    a01 := BEDC.Derived.RationalUp.IntNeg A.a01
    a10 := BEDC.Derived.RationalUp.IntNeg A.a10
    a11 := BEDC.Derived.RationalUp.IntNeg A.a11 }

def matMul (A B : Mat2) : Mat2 :=
  { a00 :=
      BEDC.Derived.RationalUp.IntAdd
        (BEDC.Derived.RationalUp.IntMul A.a00 B.a00)
        (BEDC.Derived.RationalUp.IntMul A.a01 B.a10)
    a01 :=
      BEDC.Derived.RationalUp.IntAdd
        (BEDC.Derived.RationalUp.IntMul A.a00 B.a01)
        (BEDC.Derived.RationalUp.IntMul A.a01 B.a11)
    a10 :=
      BEDC.Derived.RationalUp.IntAdd
        (BEDC.Derived.RationalUp.IntMul A.a10 B.a00)
        (BEDC.Derived.RationalUp.IntMul A.a11 B.a10)
    a11 :=
      BEDC.Derived.RationalUp.IntAdd
        (BEDC.Derived.RationalUp.IntMul A.a10 B.a01)
        (BEDC.Derived.RationalUp.IntMul A.a11 B.a11) }

def det (A : Mat2) : BEDC.Derived.PrimeUp.IntegerUp :=
  BEDC.Derived.RationalUp.IntAdd
    (BEDC.Derived.RationalUp.IntMul A.a00 A.a11)
    (BEDC.Derived.RationalUp.IntNeg
      (BEDC.Derived.RationalUp.IntMul A.a01 A.a10))

private abbrev I := BEDC.Derived.PrimeUp.IntegerUp
private abbrev ieq := BEDC.Derived.RationalUp.IntEq
private abbrev iadd := BEDC.Derived.RationalUp.IntAdd
private abbrev imul := BEDC.Derived.RationalUp.IntMul
private abbrev ineg := BEDC.Derived.RationalUp.IntNeg
private abbrev izero := BEDC.Derived.RationalUp.intZero
private abbrev ione := BEDC.Derived.RationalUp.intOne

private theorem ieq_refl (x : I) : ieq x x :=
  BEDC.Derived.RationalUp.IntEq_refl x

private theorem ieq_symm {x y : I} : ieq x y -> ieq y x :=
  BEDC.Derived.RationalUp.IntEq_symm

private theorem ieq_trans {x y z : I} : ieq x y -> ieq y z -> ieq x z :=
  BEDC.Derived.RationalUp.IntEq_trans

private theorem iadd_zero_left (x : I) : ieq (iadd izero x) x :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws.zero_add x

private theorem iadd_neg_left (x : I) : ieq (iadd (ineg x) x) izero :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws.neg_add x

private theorem imul_one_left (x : I) : ieq (imul ione x) x :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws.one_mul x

private theorem imul_zero_left (x : I) : ieq (imul izero x) izero :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws.zero_mul x

theorem MatEq_refl (A : Mat2) : MatEq A A := by
  unfold MatEq
  exact ⟨ieq_refl A.a00, ieq_refl A.a01, ieq_refl A.a10, ieq_refl A.a11⟩

theorem MatEq_symm {A B : Mat2} : MatEq A B -> MatEq B A := by
  intro same
  unfold MatEq at same ⊢
  exact
    ⟨ieq_symm same.left,
      ieq_symm same.right.left,
      ieq_symm same.right.right.left,
      ieq_symm same.right.right.right⟩

theorem MatEq_trans {A B C : Mat2} : MatEq A B -> MatEq B C -> MatEq A C := by
  intro left right
  unfold MatEq at left right ⊢
  exact
    ⟨ieq_trans left.left right.left,
      ieq_trans left.right.left right.right.left,
      ieq_trans left.right.right.left right.right.right.left,
      ieq_trans left.right.right.right right.right.right.right⟩

theorem matAdd_respects {A A' B B' : Mat2} :
    MatEq A A' -> MatEq B B' -> MatEq (matAdd A B) (matAdd A' B') := by
  intro left right
  unfold MatEq at left right ⊢
  unfold matAdd
  exact
    ⟨BEDC.Derived.IntUp.IntAdd_respects left.left right.left,
      BEDC.Derived.IntUp.IntAdd_respects left.right.left right.right.left,
      BEDC.Derived.IntUp.IntAdd_respects left.right.right.left right.right.right.left,
      BEDC.Derived.IntUp.IntAdd_respects left.right.right.right right.right.right.right⟩

theorem matNeg_respects {A B : Mat2} :
    MatEq A B -> MatEq (matNeg A) (matNeg B) := by
  intro same
  unfold MatEq at same ⊢
  unfold matNeg
  exact
    ⟨BEDC.Derived.IntUp.IntNeg_respects same.left,
      BEDC.Derived.IntUp.IntNeg_respects same.right.left,
      BEDC.Derived.IntUp.IntNeg_respects same.right.right.left,
      BEDC.Derived.IntUp.IntNeg_respects same.right.right.right⟩

theorem matAdd_comm (A B : Mat2) : MatEq (matAdd A B) (matAdd B A) := by
  unfold MatEq matAdd
  exact
    ⟨BEDC.Derived.IntUp.IntAdd_comm A.a00 B.a00,
      BEDC.Derived.IntUp.IntAdd_comm A.a01 B.a01,
      BEDC.Derived.IntUp.IntAdd_comm A.a10 B.a10,
      BEDC.Derived.IntUp.IntAdd_comm A.a11 B.a11⟩

theorem matAdd_assoc (A B C : Mat2) :
    MatEq (matAdd (matAdd A B) C) (matAdd A (matAdd B C)) := by
  unfold MatEq matAdd
  exact
    ⟨BEDC.Derived.IntUp.IntAdd_assoc A.a00 B.a00 C.a00,
      BEDC.Derived.IntUp.IntAdd_assoc A.a01 B.a01 C.a01,
      BEDC.Derived.IntUp.IntAdd_assoc A.a10 B.a10 C.a10,
      BEDC.Derived.IntUp.IntAdd_assoc A.a11 B.a11 C.a11⟩

theorem matAdd_zero (A : Mat2) : MatEq (matAdd A matZero) A := by
  unfold MatEq matAdd matZero
  exact
    ⟨BEDC.Derived.IntUp.IntAdd_zero A.a00,
      BEDC.Derived.IntUp.IntAdd_zero A.a01,
      BEDC.Derived.IntUp.IntAdd_zero A.a10,
      BEDC.Derived.IntUp.IntAdd_zero A.a11⟩

theorem matZero_add (A : Mat2) : MatEq (matAdd matZero A) A := by
  unfold MatEq matAdd matZero
  exact
    ⟨iadd_zero_left A.a00,
      iadd_zero_left A.a01,
      iadd_zero_left A.a10,
      iadd_zero_left A.a11⟩

theorem matAdd_neg (A : Mat2) : MatEq (matAdd A (matNeg A)) matZero := by
  unfold MatEq matAdd matNeg matZero
  exact
    ⟨BEDC.Derived.IntUp.IntAdd_neg A.a00,
      BEDC.Derived.IntUp.IntAdd_neg A.a01,
      BEDC.Derived.IntUp.IntAdd_neg A.a10,
      BEDC.Derived.IntUp.IntAdd_neg A.a11⟩

theorem matNeg_add (A : Mat2) : MatEq (matAdd (matNeg A) A) matZero := by
  unfold MatEq matAdd matNeg matZero
  exact
    ⟨iadd_neg_left A.a00,
      iadd_neg_left A.a01,
      iadd_neg_left A.a10,
      iadd_neg_left A.a11⟩

private theorem scalar_add_three_context {a a' b b' c c' : I} :
    ieq a a' -> ieq b b' -> ieq c c' ->
      ieq (iadd (iadd a b) c) (iadd (iadd a' b') c') := by
  intro ha hb hc
  exact BEDC.Derived.IntUp.IntAdd_respects
    (BEDC.Derived.IntUp.IntAdd_respects ha hb) hc

private theorem scalar_add_four_context {a a' b b' c c' d d' : I} :
    ieq a a' -> ieq b b' -> ieq c c' -> ieq d d' ->
      ieq (iadd (iadd a b) (iadd c d)) (iadd (iadd a' b') (iadd c' d')) := by
  intro ha hb hc hd
  exact BEDC.Derived.IntUp.IntAdd_respects
    (BEDC.Derived.IntUp.IntAdd_respects ha hb)
    (BEDC.Derived.IntUp.IntAdd_respects hc hd)

private theorem scalar_add_left_right_swap (a b c : I) :
    ieq (iadd a (iadd b c)) (iadd b (iadd a c)) := by
  exact ieq_trans (ieq_symm (BEDC.Derived.IntUp.IntAdd_assoc a b c))
    (ieq_trans
      (BEDC.Derived.IntUp.IntAdd_respects
        (BEDC.Derived.IntUp.IntAdd_comm a b) (ieq_refl c))
      (BEDC.Derived.IntUp.IntAdd_assoc b a c))

private theorem scalar_add_middle_four (a b c d : I) :
    ieq (iadd (iadd a b) (iadd c d)) (iadd (iadd a c) (iadd b d)) := by
  exact ieq_trans (BEDC.Derived.IntUp.IntAdd_assoc a b (iadd c d))
    (ieq_trans
      (BEDC.Derived.IntUp.IntAdd_respects (ieq_refl a)
        (scalar_add_left_right_swap b c d))
      (ieq_symm (BEDC.Derived.IntUp.IntAdd_assoc a c (iadd b d))))

private theorem scalar_mul_middle_four (a b c d : I) :
    ieq (imul (imul a b) (imul c d)) (imul (imul a c) (imul b d)) :=
  BEDC.Derived.RationalUp.intMul_two_by_two_swap a b c d

private theorem scalar_add_right_zero (x : I) : ieq (iadd x izero) x :=
  BEDC.Derived.IntUp.IntAdd_zero x

private theorem scalar_add_right_inverse (x : I) : ieq (iadd x (ineg x)) izero :=
  BEDC.Derived.IntUp.IntAdd_neg x

private theorem scalar_left_inverse_unique {z x : I} :
    ieq (iadd z x) izero -> ieq z (ineg x) := by
  intro hz
  have start : ieq z (iadd izero z) := ieq_symm (iadd_zero_left z)
  have insert : ieq (iadd izero z) (iadd (iadd (ineg x) x) z) := by
    exact BEDC.Derived.IntUp.IntAdd_respects (ieq_symm (iadd_neg_left x)) (ieq_refl z)
  have assoc1 : ieq (iadd (iadd (ineg x) x) z) (iadd (ineg x) (iadd x z)) :=
    BEDC.Derived.IntUp.IntAdd_assoc (ineg x) x z
  have swapXZ : ieq (iadd x z) (iadd z x) :=
    BEDC.Derived.IntUp.IntAdd_comm x z
  have useHz : ieq (iadd (ineg x) (iadd x z)) (iadd (ineg x) izero) := by
    exact BEDC.Derived.IntUp.IntAdd_respects (ieq_refl (ineg x)) (ieq_trans swapXZ hz)
  exact ieq_trans start
    (ieq_trans insert
      (ieq_trans assoc1 (ieq_trans useHz (scalar_add_right_zero (ineg x)))))

private theorem scalar_inverse_transport_right {p q : I} :
    ieq p q -> ieq (iadd p (ineg q)) izero := by
  intro hpq
  exact ieq_trans
    (BEDC.Derived.IntUp.IntAdd_respects (ieq_refl p)
      (BEDC.Derived.IntUp.IntNeg_respects (ieq_symm hpq)))
    (scalar_add_right_inverse p)

private theorem scalar_neg_add (x y : I) :
    ieq (ineg (iadd x y)) (iadd (ineg x) (ineg y)) := by
  apply ieq_symm
  apply scalar_left_inverse_unique
  have assoc1 :
      ieq (iadd (iadd (ineg x) (ineg y)) (iadd x y))
        (iadd (ineg x) (iadd (ineg y) (iadd x y))) :=
    BEDC.Derived.IntUp.IntAdd_assoc (ineg x) (ineg y) (iadd x y)
  have innerSwap :
      ieq (iadd (ineg y) (iadd x y)) (iadd x (iadd (ineg y) y)) := by
    exact ieq_trans (ieq_symm (BEDC.Derived.IntUp.IntAdd_assoc (ineg y) x y))
      (ieq_trans
        (BEDC.Derived.IntUp.IntAdd_respects
          (BEDC.Derived.IntUp.IntAdd_comm (ineg y) x) (ieq_refl y))
        (BEDC.Derived.IntUp.IntAdd_assoc x (ineg y) y))
  have cancelY : ieq (iadd x (iadd (ineg y) y)) (iadd x izero) := by
    exact BEDC.Derived.IntUp.IntAdd_respects (ieq_refl x) (iadd_neg_left y)
  have afterInner :
      ieq (iadd (ineg x) (iadd (ineg y) (iadd x y))) (iadd (ineg x) x) := by
    exact BEDC.Derived.IntUp.IntAdd_respects (ieq_refl (ineg x))
      (ieq_trans innerSwap (ieq_trans cancelY (scalar_add_right_zero x)))
  exact ieq_trans assoc1 (ieq_trans afterInner (iadd_neg_left x))

private theorem scalar_neg_involutive (x : I) : ieq (ineg (ineg x)) x :=
  ieq_symm
    (scalar_left_inverse_unique (z := x) (x := ineg x) (scalar_add_right_inverse x))

private theorem scalar_mul_neg_right (x y : I) :
    ieq (imul x (ineg y)) (ineg (imul x y)) := by
  apply scalar_left_inverse_unique
  have distrib :
      ieq (imul x (iadd (ineg y) y))
        (iadd (imul x (ineg y)) (imul x y)) :=
    BEDC.Derived.IntUp.IntMul_add_distrib x (ineg y) y
  have zeroArg : ieq (imul x (iadd (ineg y) y)) (imul x izero) := by
    exact BEDC.Derived.IntUp.IntMul_respects (ieq_refl x) (iadd_neg_left y)
  exact ieq_trans (ieq_symm distrib)
    (ieq_trans zeroArg (BEDC.Derived.IntUp.IntMul_zero x))

private theorem scalar_mul_neg_left (x y : I) :
    ieq (imul (ineg x) y) (ineg (imul x y)) := by
  exact ieq_trans (BEDC.Derived.IntUp.IntMul_comm (ineg x) y)
    (ieq_trans (scalar_mul_neg_right y x)
      (BEDC.Derived.IntUp.IntNeg_respects (BEDC.Derived.IntUp.IntMul_comm y x)))

private theorem scalar_mul_neg_neg (x y : I) :
    ieq (imul (ineg x) (ineg y)) (imul x y) := by
  exact ieq_trans (scalar_mul_neg_left x (ineg y))
    (ieq_trans
      (BEDC.Derived.IntUp.IntNeg_respects (scalar_mul_neg_right x y))
      (scalar_neg_involutive (imul x y)))

private theorem scalar_mul_one_add_mul_zero (x y : I) :
    ieq (iadd (imul x ione) (imul y izero)) x := by
  exact ieq_trans
    (BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_one x) (BEDC.Derived.IntUp.IntMul_zero y))
    (BEDC.Derived.IntUp.IntAdd_zero x)

private theorem scalar_mul_zero_add_mul_one (x y : I) :
    ieq (iadd (imul x izero) (imul y ione)) y := by
  exact ieq_trans
    (BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_zero x) (BEDC.Derived.IntUp.IntMul_one y))
    (iadd_zero_left y)

private theorem scalar_one_mul_add_zero_mul (x y : I) :
    ieq (iadd (imul ione x) (imul izero y)) x := by
  exact ieq_trans
    (BEDC.Derived.IntUp.IntAdd_respects (imul_one_left x) (imul_zero_left y))
    (BEDC.Derived.IntUp.IntAdd_zero x)

private theorem scalar_zero_mul_add_one_mul (x y : I) :
    ieq (iadd (imul izero x) (imul ione y)) y := by
  exact ieq_trans
    (BEDC.Derived.IntUp.IntAdd_respects (imul_zero_left x) (imul_one_left y))
    (iadd_zero_left y)

private theorem scalar_matrix_assoc_entry
    (a c b d f g e h : I) :
    ieq
      (iadd
        (imul (iadd (imul a b) (imul c d)) e)
        (imul (iadd (imul a f) (imul c g)) h))
      (iadd
        (imul a (iadd (imul b e) (imul f h)))
        (imul c (iadd (imul d e) (imul g h)))) := by
  have leftExpanded :
      ieq
        (iadd
          (imul (iadd (imul a b) (imul c d)) e)
          (imul (iadd (imul a f) (imul c g)) h))
        (iadd
          (iadd (imul (imul a b) e) (imul (imul c d) e))
          (iadd (imul (imul a f) h) (imul (imul c g) h))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_add_distrib_right (imul a b) (imul c d) e)
      (BEDC.Derived.IntUp.IntMul_add_distrib_right (imul a f) (imul c g) h)
  have regroup :
      ieq
        (iadd
          (iadd (imul (imul a b) e) (imul (imul c d) e))
          (iadd (imul (imul a f) h) (imul (imul c g) h)))
        (iadd
          (iadd (imul (imul a b) e) (imul (imul a f) h))
          (iadd (imul (imul c d) e) (imul (imul c g) h))) :=
    scalar_add_middle_four
      (imul (imul a b) e) (imul (imul c d) e)
      (imul (imul a f) h) (imul (imul c g) h)
  have reassoc :
      ieq
        (iadd
          (iadd (imul (imul a b) e) (imul (imul a f) h))
          (iadd (imul (imul c d) e) (imul (imul c g) h)))
        (iadd
          (iadd (imul a (imul b e)) (imul a (imul f h)))
          (iadd (imul c (imul d e)) (imul c (imul g h)))) := by
    exact scalar_add_four_context
      (BEDC.Derived.IntUp.IntMul_assoc a b e)
      (BEDC.Derived.IntUp.IntMul_assoc a f h)
      (BEDC.Derived.IntUp.IntMul_assoc c d e)
      (BEDC.Derived.IntUp.IntMul_assoc c g h)
  have collect :
      ieq
        (iadd
          (iadd (imul a (imul b e)) (imul a (imul f h)))
          (iadd (imul c (imul d e)) (imul c (imul g h))))
        (iadd
          (imul a (iadd (imul b e) (imul f h)))
          (imul c (iadd (imul d e) (imul g h)))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (ieq_symm (BEDC.Derived.IntUp.IntMul_add_distrib a (imul b e) (imul f h)))
      (ieq_symm (BEDC.Derived.IntUp.IntMul_add_distrib c (imul d e) (imul g h)))
  exact ieq_trans leftExpanded (ieq_trans regroup (ieq_trans reassoc collect))

private theorem scalar_matrix_left_distrib_entry
    (a c b d e f : I) :
    ieq
      (iadd (imul a (iadd b d)) (imul c (iadd e f)))
      (iadd (iadd (imul a b) (imul c e)) (iadd (imul a d) (imul c f))) := by
  have expanded :
      ieq
        (iadd (imul a (iadd b d)) (imul c (iadd e f)))
        (iadd (iadd (imul a b) (imul a d)) (iadd (imul c e) (imul c f))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_add_distrib a b d)
      (BEDC.Derived.IntUp.IntMul_add_distrib c e f)
  exact ieq_trans expanded
    (scalar_add_middle_four (imul a b) (imul a d) (imul c e) (imul c f))

private theorem scalar_matrix_right_distrib_entry
    (a b c d e f : I) :
    ieq
      (iadd (imul (iadd a b) e) (imul (iadd c d) f))
      (iadd (iadd (imul a e) (imul c f)) (iadd (imul b e) (imul d f))) := by
  have expanded :
      ieq
        (iadd (imul (iadd a b) e) (imul (iadd c d) f))
        (iadd (iadd (imul a e) (imul b e)) (iadd (imul c f) (imul d f))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_add_distrib_right a b e)
      (BEDC.Derived.IntUp.IntMul_add_distrib_right c d f)
  exact ieq_trans expanded
    (scalar_add_middle_four (imul a e) (imul b e) (imul c f) (imul d f))

private theorem scalar_mul_add_add_row_expand (x y u v : I) :
    ieq (imul (iadd x y) (iadd u v))
      (iadd (iadd (imul x u) (imul x v)) (iadd (imul y u) (imul y v))) := by
  have rightExpanded :
      ieq (imul (iadd x y) (iadd u v))
        (iadd (imul (iadd x y) u) (imul (iadd x y) v)) :=
    BEDC.Derived.IntUp.IntMul_add_distrib (iadd x y) u v
  have leftExpanded :
      ieq (iadd (imul (iadd x y) u) (imul (iadd x y) v))
        (iadd (iadd (imul x u) (imul y u)) (iadd (imul x v) (imul y v))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_add_distrib_right x y u)
      (BEDC.Derived.IntUp.IntMul_add_distrib_right x y v)
  have regroup :
      ieq (iadd (iadd (imul x u) (imul y u)) (iadd (imul x v) (imul y v)))
        (iadd (iadd (imul x u) (imul x v)) (iadd (imul y u) (imul y v))) :=
    scalar_add_middle_four (imul x u) (imul y u) (imul x v) (imul y v)
  exact ieq_trans rightExpanded (ieq_trans leftExpanded regroup)

theorem matMul_respects {A A' B B' : Mat2} :
    MatEq A A' -> MatEq B B' -> MatEq (matMul A B) (matMul A' B') := by
  intro left right
  unfold MatEq at left right ⊢
  unfold matMul
  exact
    ⟨BEDC.Derived.IntUp.IntAdd_respects
        (BEDC.Derived.IntUp.IntMul_respects left.left right.left)
        (BEDC.Derived.IntUp.IntMul_respects left.right.left right.right.right.left),
      BEDC.Derived.IntUp.IntAdd_respects
        (BEDC.Derived.IntUp.IntMul_respects left.left right.right.left)
        (BEDC.Derived.IntUp.IntMul_respects left.right.left right.right.right.right),
      BEDC.Derived.IntUp.IntAdd_respects
        (BEDC.Derived.IntUp.IntMul_respects left.right.right.left right.left)
        (BEDC.Derived.IntUp.IntMul_respects left.right.right.right right.right.right.left),
      BEDC.Derived.IntUp.IntAdd_respects
        (BEDC.Derived.IntUp.IntMul_respects left.right.right.left right.right.left)
        (BEDC.Derived.IntUp.IntMul_respects left.right.right.right right.right.right.right)⟩

theorem matMul_one (A : Mat2) : MatEq (matMul A matOne) A := by
  unfold MatEq matMul matOne
  exact
    ⟨scalar_mul_one_add_mul_zero A.a00 A.a01,
      scalar_mul_zero_add_mul_one A.a00 A.a01,
      scalar_mul_one_add_mul_zero A.a10 A.a11,
      scalar_mul_zero_add_mul_one A.a10 A.a11⟩

theorem matOne_mul (A : Mat2) : MatEq (matMul matOne A) A := by
  unfold MatEq matMul matOne
  exact
    ⟨scalar_one_mul_add_zero_mul A.a00 A.a10,
      scalar_one_mul_add_zero_mul A.a01 A.a11,
      scalar_zero_mul_add_one_mul A.a00 A.a10,
      scalar_zero_mul_add_one_mul A.a01 A.a11⟩

theorem matMul_assoc (A B C : Mat2) :
    MatEq (matMul (matMul A B) C) (matMul A (matMul B C)) := by
  unfold MatEq matMul
  exact
    ⟨scalar_matrix_assoc_entry A.a00 A.a01 B.a00 B.a10 B.a01 B.a11 C.a00 C.a10,
      scalar_matrix_assoc_entry A.a00 A.a01 B.a00 B.a10 B.a01 B.a11 C.a01 C.a11,
      scalar_matrix_assoc_entry A.a10 A.a11 B.a00 B.a10 B.a01 B.a11 C.a00 C.a10,
      scalar_matrix_assoc_entry A.a10 A.a11 B.a00 B.a10 B.a01 B.a11 C.a01 C.a11⟩

theorem matMul_add_distrib (A B C : Mat2) :
    MatEq (matMul A (matAdd B C))
      (matAdd (matMul A B) (matMul A C)) := by
  unfold MatEq matMul matAdd
  exact
    ⟨scalar_matrix_left_distrib_entry A.a00 A.a01 B.a00 C.a00 B.a10 C.a10,
      scalar_matrix_left_distrib_entry A.a00 A.a01 B.a01 C.a01 B.a11 C.a11,
      scalar_matrix_left_distrib_entry A.a10 A.a11 B.a00 C.a00 B.a10 C.a10,
      scalar_matrix_left_distrib_entry A.a10 A.a11 B.a01 C.a01 B.a11 C.a11⟩

theorem matAdd_mul_distrib (A B C : Mat2) :
    MatEq (matMul (matAdd A B) C)
      (matAdd (matMul A C) (matMul B C)) := by
  unfold MatEq matMul matAdd
  exact
    ⟨scalar_matrix_right_distrib_entry A.a00 B.a00 A.a01 B.a01 C.a00 C.a10,
      scalar_matrix_right_distrib_entry A.a00 B.a00 A.a01 B.a01 C.a01 C.a11,
      scalar_matrix_right_distrib_entry A.a10 B.a10 A.a11 B.a11 C.a00 C.a10,
      scalar_matrix_right_distrib_entry A.a10 B.a10 A.a11 B.a11 C.a01 C.a11⟩

structure Mat2RingLaws where
  eq_refl : ∀ A : Mat2, MatEq A A
  eq_symm : ∀ {A B : Mat2}, MatEq A B -> MatEq B A
  eq_trans : ∀ {A B C : Mat2}, MatEq A B -> MatEq B C -> MatEq A C
  add_respects :
    ∀ {A A' B B' : Mat2}, MatEq A A' -> MatEq B B' ->
      MatEq (matAdd A B) (matAdd A' B')
  mul_respects :
    ∀ {A A' B B' : Mat2}, MatEq A A' -> MatEq B B' ->
      MatEq (matMul A B) (matMul A' B')
  neg_respects : ∀ {A B : Mat2}, MatEq A B -> MatEq (matNeg A) (matNeg B)
  add_comm : ∀ A B : Mat2, MatEq (matAdd A B) (matAdd B A)
  add_assoc :
    ∀ A B C : Mat2, MatEq (matAdd (matAdd A B) C) (matAdd A (matAdd B C))
  add_zero : ∀ A : Mat2, MatEq (matAdd A matZero) A
  zero_add : ∀ A : Mat2, MatEq (matAdd matZero A) A
  add_neg : ∀ A : Mat2, MatEq (matAdd A (matNeg A)) matZero
  neg_add : ∀ A : Mat2, MatEq (matAdd (matNeg A) A) matZero
  mul_assoc :
    ∀ A B C : Mat2, MatEq (matMul (matMul A B) C) (matMul A (matMul B C))
  mul_one : ∀ A : Mat2, MatEq (matMul A matOne) A
  one_mul : ∀ A : Mat2, MatEq (matMul matOne A) A
  left_distrib :
    ∀ A B C : Mat2,
      MatEq (matMul A (matAdd B C)) (matAdd (matMul A B) (matMul A C))
  right_distrib :
    ∀ A B C : Mat2,
      MatEq (matMul (matAdd A B) C) (matAdd (matMul A C) (matMul B C))

def Mat2_ring_laws : Mat2RingLaws where
  eq_refl := MatEq_refl
  eq_symm := by
    intro A B
    exact MatEq_symm
  eq_trans := by
    intro A B C
    exact MatEq_trans
  add_respects := by
    intro A A' B B'
    exact matAdd_respects
  mul_respects := by
    intro A A' B B'
    exact matMul_respects
  neg_respects := by
    intro A B
    exact matNeg_respects
  add_comm := matAdd_comm
  add_assoc := matAdd_assoc
  add_zero := matAdd_zero
  zero_add := matZero_add
  add_neg := matAdd_neg
  neg_add := matNeg_add
  mul_assoc := matMul_assoc
  mul_one := matMul_one
  one_mul := matOne_mul
  left_distrib := matMul_add_distrib
  right_distrib := matAdd_mul_distrib

theorem det_respects {A B : Mat2} : MatEq A B -> ieq (det A) (det B) := by
  intro same
  unfold MatEq at same
  unfold det
  exact BEDC.Derived.IntUp.IntAdd_respects
    (BEDC.Derived.IntUp.IntMul_respects same.left same.right.right.right)
    (BEDC.Derived.IntUp.IntNeg_respects
      (BEDC.Derived.IntUp.IntMul_respects same.right.left same.right.right.left))

private theorem scalar_eight_cancel
    {p1 p2 p3 p4 q1 q2 q3 q4 : I} :
    ieq p1 q1 -> ieq p4 q4 ->
      ieq
        (iadd (iadd (iadd p1 p2) (iadd p3 p4))
          (iadd (iadd (ineg q1) (ineg q2)) (iadd (ineg q3) (ineg q4))))
        (iadd (iadd p2 (ineg q2)) (iadd p3 (ineg q3))) := by
  intro hp1 hq4
  have outer :=
    scalar_add_middle_four (iadd p1 p2) (iadd p3 p4)
      (iadd (ineg q1) (ineg q2)) (iadd (ineg q3) (ineg q4))
  have inner :
      ieq
        (iadd (iadd (iadd p1 p2) (iadd (ineg q1) (ineg q2)))
          (iadd (iadd p3 p4) (iadd (ineg q3) (ineg q4))))
        (iadd (iadd (iadd p1 (ineg q1)) (iadd p2 (ineg q2)))
          (iadd (iadd p3 (ineg q3)) (iadd p4 (ineg q4)))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (scalar_add_middle_four p1 p2 (ineg q1) (ineg q2))
      (scalar_add_middle_four p3 p4 (ineg q3) (ineg q4))
  have cancelEnds :
      ieq
        (iadd (iadd (iadd p1 (ineg q1)) (iadd p2 (ineg q2)))
          (iadd (iadd p3 (ineg q3)) (iadd p4 (ineg q4))))
        (iadd (iadd izero (iadd p2 (ineg q2)))
          (iadd (iadd p3 (ineg q3)) izero)) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntAdd_respects
        (scalar_inverse_transport_right hp1) (ieq_refl (iadd p2 (ineg q2))))
      (BEDC.Derived.IntUp.IntAdd_respects
        (ieq_refl (iadd p3 (ineg q3))) (scalar_inverse_transport_right hq4))
  have eraseZeros :
      ieq
        (iadd (iadd izero (iadd p2 (ineg q2)))
          (iadd (iadd p3 (ineg q3)) izero))
        (iadd (iadd p2 (ineg q2)) (iadd p3 (ineg q3))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (iadd_zero_left (iadd p2 (ineg q2)))
      (scalar_add_right_zero (iadd p3 (ineg q3)))
  exact ieq_trans outer (ieq_trans inner (ieq_trans cancelEnds eraseZeros))

private theorem scalar_det_product_expand (a b c d e f g h : I) :
    ieq
      (imul (iadd (imul a d) (ineg (imul b c)))
        (iadd (imul e h) (ineg (imul f g))))
      (iadd
        (iadd (imul (imul a d) (imul e h))
          (ineg (imul (imul a d) (imul f g))))
        (iadd (imul (imul b c) (imul f g))
          (ineg (imul (imul b c) (imul e h))))) := by
  let X := imul (imul a d) (imul e h)
  let Y := imul (imul a d) (imul f g)
  let Z := imul (imul b c) (imul f g)
  let W := imul (imul b c) (imul e h)
  have expanded :
      ieq
        (imul (iadd (imul a d) (ineg (imul b c)))
          (iadd (imul e h) (ineg (imul f g))))
        (iadd
          (iadd X (imul (imul a d) (ineg (imul f g))))
          (iadd (imul (ineg (imul b c)) (imul e h))
            (imul (ineg (imul b c)) (ineg (imul f g))))) := by
    exact scalar_mul_add_add_row_expand
      (imul a d) (ineg (imul b c)) (imul e h) (ineg (imul f g))
  have normalized :
      ieq
        (iadd
          (iadd X (imul (imul a d) (ineg (imul f g))))
          (iadd (imul (ineg (imul b c)) (imul e h))
            (imul (ineg (imul b c)) (ineg (imul f g)))))
        (iadd (iadd X (ineg Y)) (iadd (ineg W) Z)) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntAdd_respects (ieq_refl X)
        (scalar_mul_neg_right (imul a d) (imul f g)))
      (BEDC.Derived.IntUp.IntAdd_respects
        (scalar_mul_neg_left (imul b c) (imul e h))
        (scalar_mul_neg_neg (imul b c) (imul f g)))
  have swapTail :
      ieq (iadd (iadd X (ineg Y)) (iadd (ineg W) Z))
        (iadd (iadd X (ineg Y)) (iadd Z (ineg W))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects (ieq_refl (iadd X (ineg Y)))
      (BEDC.Derived.IntUp.IntAdd_comm (ineg W) Z)
  exact ieq_trans expanded (ieq_trans normalized swapTail)

private theorem scalar_det_mul_core (a b c d e f g h : I) :
    ieq
      (iadd
        (imul (iadd (imul a e) (imul b g)) (iadd (imul c f) (imul d h)))
        (ineg (imul (iadd (imul a f) (imul b h)) (iadd (imul c e) (imul d g)))))
      (iadd
        (iadd (imul (imul a d) (imul e h))
          (ineg (imul (imul a d) (imul f g))))
        (iadd (imul (imul b c) (imul f g))
          (ineg (imul (imul b c) (imul e h))))) := by
  let p1 := imul (imul a e) (imul c f)
  let p2 := imul (imul a e) (imul d h)
  let p3 := imul (imul b g) (imul c f)
  let p4 := imul (imul b g) (imul d h)
  let q1 := imul (imul a f) (imul c e)
  let q2 := imul (imul a f) (imul d g)
  let q3 := imul (imul b h) (imul c e)
  let q4 := imul (imul b h) (imul d g)
  let X := imul (imul a d) (imul e h)
  let Y := imul (imul a d) (imul f g)
  let Z := imul (imul b c) (imul f g)
  let W := imul (imul b c) (imul e h)
  have leftExpand :
      ieq
        (imul (iadd (imul a e) (imul b g)) (iadd (imul c f) (imul d h)))
        (iadd (iadd p1 p2) (iadd p3 p4)) := by
    exact scalar_mul_add_add_row_expand (imul a e) (imul b g) (imul c f) (imul d h)
  have rightExpand :
      ieq
        (imul (iadd (imul a f) (imul b h)) (iadd (imul c e) (imul d g)))
        (iadd (iadd q1 q2) (iadd q3 q4)) := by
    exact scalar_mul_add_add_row_expand (imul a f) (imul b h) (imul c e) (imul d g)
  have expanded :
      ieq
        (iadd
          (imul (iadd (imul a e) (imul b g)) (iadd (imul c f) (imul d h)))
          (ineg (imul (iadd (imul a f) (imul b h)) (iadd (imul c e) (imul d g)))))
        (iadd (iadd (iadd p1 p2) (iadd p3 p4))
          (ineg (iadd (iadd q1 q2) (iadd q3 q4)))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects leftExpand
      (BEDC.Derived.IntUp.IntNeg_respects rightExpand)
  have negExpanded :
      ieq (ineg (iadd (iadd q1 q2) (iadd q3 q4)))
        (iadd (iadd (ineg q1) (ineg q2)) (iadd (ineg q3) (ineg q4))) := by
    exact ieq_trans (scalar_neg_add (iadd q1 q2) (iadd q3 q4))
      (BEDC.Derived.IntUp.IntAdd_respects (scalar_neg_add q1 q2) (scalar_neg_add q3 q4))
  have normalizedNeg :
      ieq
        (iadd (iadd (iadd p1 p2) (iadd p3 p4))
          (ineg (iadd (iadd q1 q2) (iadd q3 q4))))
        (iadd (iadd (iadd p1 p2) (iadd p3 p4))
          (iadd (iadd (ineg q1) (ineg q2)) (iadd (ineg q3) (ineg q4)))) := by
    exact BEDC.Derived.IntUp.IntAdd_respects
      (ieq_refl (iadd (iadd p1 p2) (iadd p3 p4))) negExpanded
  have cancelEnds :
      ieq
        (iadd (iadd (iadd p1 p2) (iadd p3 p4))
          (iadd (iadd (ineg q1) (ineg q2)) (iadd (ineg q3) (ineg q4))))
        (iadd (iadd p2 (ineg q2)) (iadd p3 (ineg q3))) := by
    have sameP1Q1 : ieq p1 q1 := by
      unfold p1 q1
      exact ieq_trans (scalar_mul_middle_four a e c f)
        (ieq_trans
          (BEDC.Derived.IntUp.IntMul_respects
            (ieq_refl (imul a c)) (BEDC.Derived.IntUp.IntMul_comm e f))
          (ieq_symm (scalar_mul_middle_four a f c e)))
    have sameP4Q4 : ieq p4 q4 := by
      unfold p4 q4
      exact ieq_trans (scalar_mul_middle_four b g d h)
        (ieq_trans
          (BEDC.Derived.IntUp.IntMul_respects
            (ieq_refl (imul b d)) (BEDC.Derived.IntUp.IntMul_comm g h))
          (ieq_symm (scalar_mul_middle_four b h d g)))
    exact scalar_eight_cancel sameP1Q1 sameP4Q4
  have middleTargets :
      ieq (iadd (iadd p2 (ineg q2)) (iadd p3 (ineg q3)))
        (iadd (iadd X (ineg Y)) (iadd Z (ineg W))) := by
    have p2Target : ieq p2 X := by
      unfold p2 X
      exact scalar_mul_middle_four a e d h
    have q2Target : ieq q2 Y := by
      unfold q2 Y
      exact scalar_mul_middle_four a f d g
    have p3Target : ieq p3 Z := by
      unfold p3 Z
      exact ieq_trans (scalar_mul_middle_four b g c f)
        (BEDC.Derived.IntUp.IntMul_respects
          (ieq_refl (imul b c)) (BEDC.Derived.IntUp.IntMul_comm g f))
    have q3Target : ieq q3 W := by
      unfold q3 W
      exact ieq_trans (scalar_mul_middle_four b h c e)
        (BEDC.Derived.IntUp.IntMul_respects
          (ieq_refl (imul b c)) (BEDC.Derived.IntUp.IntMul_comm h e))
    exact scalar_add_four_context p2Target
      (BEDC.Derived.IntUp.IntNeg_respects q2Target) p3Target
      (BEDC.Derived.IntUp.IntNeg_respects q3Target)
  exact ieq_trans expanded
    (ieq_trans normalizedNeg (ieq_trans cancelEnds middleTargets))

theorem det_mul (A B : Mat2) :
    ieq (det (matMul A B)) (imul (det A) (det B)) := by
  unfold det matMul
  exact ieq_trans
    (scalar_det_mul_core A.a00 A.a01 A.a10 A.a11 B.a00 B.a01 B.a10 B.a11)
    (ieq_symm (scalar_det_product_expand A.a00 A.a01 A.a10 A.a11 B.a00 B.a01 B.a10 B.a11))

end BEDC.Derived.MatrixUp
