import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def LinearMapSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def LinearMapSingletonClassifier (h k : BHist) : Prop :=
  LinearMapSingletonCarrier h ∧ LinearMapSingletonCarrier k ∧ hsame h k

def LinearMapSingletonComp (_g _f : BHist) : BHist :=
  BHist.Empty

def LinearMapSingletonEval (_f _x : BHist) : BHist :=
  BHist.Empty

theorem LinearMapSingleton_empty_history_laws :
    SemanticNameCert LinearMapSingletonCarrier LinearMapSingletonCarrier
      LinearMapSingletonCarrier LinearMapSingletonClassifier ∧
      LinearMapSingletonCarrier BHist.Empty ∧
      (forall {f x : BHist}, LinearMapSingletonCarrier f -> LinearMapSingletonCarrier x ->
        LinearMapSingletonCarrier (LinearMapSingletonEval f x) ∧
          LinearMapSingletonClassifier (LinearMapSingletonEval f x) BHist.Empty) ∧
      (forall {g f : BHist}, LinearMapSingletonCarrier g -> LinearMapSingletonCarrier f ->
        LinearMapSingletonCarrier (LinearMapSingletonComp g f)) ∧
      (forall {f g x y : BHist}, LinearMapSingletonClassifier f g ->
        LinearMapSingletonClassifier x y ->
          LinearMapSingletonClassifier (LinearMapSingletonEval f x)
            (LinearMapSingletonEval g y)) := by
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : LinearMapSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
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
  · constructor
    · exact emptyCarrier
    · constructor
      · intro f x _carrierF _carrierX
        exact And.intro emptyCarrier emptyClassifier
      · constructor
        · intro g f _carrierG _carrierF
          exact emptyCarrier
        · intro f g x y _sameFG _sameXY
          exact emptyClassifier

theorem LinearMapSingleton_public_empty_code_exactness {f g x : BHist} :
    LinearMapSingletonCarrier f -> LinearMapSingletonCarrier g ->
      LinearMapSingletonCarrier x ->
        LinearMapSingletonClassifier f BHist.Empty ∧
          LinearMapSingletonClassifier BHist.Empty BHist.Empty ∧
            LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty ∧
              LinearMapSingletonClassifier (LinearMapSingletonEval f x) x := by
  intro carrierF carrierG carrierX
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : LinearMapSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact And.intro carrierF (And.intro emptyCarrier carrierF)
  · constructor
    · exact emptyClassifier
    · constructor
      · exact emptyClassifier
      · exact And.intro emptyCarrier (And.intro carrierX (hsame_symm carrierX))

theorem LinearMapSingletonClassifier_append_left_cancel_iff {P Q R : BHist} :
    LinearMapSingletonCarrier P ->
      (LinearMapSingletonClassifier (append P Q) (append P R) ↔
        LinearMapSingletonClassifier Q R) := by
  intro carrierP
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.right
      (And.intro rightSplit.right
        (hsame_trans leftSplit.right (hsame_symm rightSplit.right)))
  · intro classified
    cases carrierP
    have leftCarrier : LinearMapSingletonCarrier (append BHist.Empty Q) :=
      hsame_trans (append_empty_left Q) classified.left
    have rightCarrier : LinearMapSingletonCarrier (append BHist.Empty R) :=
      hsame_trans (append_empty_left R) classified.right.left
    have sameAppend : hsame (append BHist.Empty Q) (append BHist.Empty R) :=
      hsame_trans (append_empty_left Q)
        (hsame_trans classified.right.right (hsame_symm (append_empty_left R)))
    exact And.intro leftCarrier (And.intro rightCarrier sameAppend)

theorem LinearMapSingletonClassifier_append_right_cancel_iff {P Q R : BHist} :
    LinearMapSingletonCarrier P ->
      (LinearMapSingletonClassifier (append Q P) (append R P) ↔
        LinearMapSingletonClassifier Q R) := by
  intro carrierP
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.left
      (And.intro rightSplit.left
        (hsame_trans leftSplit.left (hsame_symm rightSplit.left)))
  · intro classified
    have leftCarrier : LinearMapSingletonCarrier (append Q P) :=
      append_eq_empty_iff.mpr (And.intro classified.left carrierP)
    have rightCarrier : LinearMapSingletonCarrier (append R P) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierP)
    have sameAppend : hsame (append Q P) (append R P) :=
      hsame_trans leftCarrier (hsame_symm rightCarrier)
    exact And.intro leftCarrier (And.intro rightCarrier sameAppend)

theorem LinearMapSingletonClassifier_append_two_sided_cancel_iff {P Q R S : BHist} :
    LinearMapSingletonCarrier P ->
      LinearMapSingletonCarrier S ->
        (LinearMapSingletonClassifier (append P Q) (append R S) ↔
          LinearMapSingletonClassifier Q R) := by
  intro carrierP carrierS
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.right
      (And.intro rightSplit.left
        (hsame_trans leftSplit.right (hsame_symm rightSplit.left)))
  · intro classified
    have leftCarrier : LinearMapSingletonCarrier (append P Q) :=
      append_eq_empty_iff.mpr (And.intro carrierP classified.left)
    have rightCarrier : LinearMapSingletonCarrier (append R S) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierS)
    have sameAppend : hsame (append P Q) (append R S) :=
      hsame_trans leftCarrier (hsame_symm rightCarrier)
    exact And.intro leftCarrier (And.intro rightCarrier sameAppend)

theorem LinearMapSingletonEval_append_input_classifier_iff {f x y h : BHist} :
    LinearMapSingletonClassifier (LinearMapSingletonEval f (append x y)) h ↔
      LinearMapSingletonCarrier h := by
  constructor
  · intro classified
    exact classified.right.left
  · intro carrierH
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro carrierH (hsame_symm carrierH))

theorem LinearMapSingletonEval_append_context_classifier_iff {p f x h : BHist} :
    LinearMapSingletonClassifier (append p (LinearMapSingletonEval f x)) h ↔
      LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier h := by
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    exact And.intro leftSplit.left classified.right.left
  · intro carriers
    have evalCarrier : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
      hsame_refl BHist.Empty
    have appendCarrier : LinearMapSingletonCarrier (append p (LinearMapSingletonEval f x)) :=
      append_eq_empty_iff.mpr (And.intro carriers.left evalCarrier)
    exact And.intro appendCarrier
      (And.intro carriers.right (hsame_trans appendCarrier (hsame_symm carriers.right)))

theorem LinearMapSingleton_laws :
    SemanticNameCert LinearMapSingletonCarrier LinearMapSingletonCarrier LinearMapSingletonCarrier LinearMapSingletonClassifier ∧
      LinearMapSingletonCarrier BHist.Empty ∧
      (∀ {f x : BHist}, LinearMapSingletonCarrier f -> LinearMapSingletonCarrier x -> LinearMapSingletonCarrier (LinearMapSingletonEval f x)) ∧
      (∀ {f g x y : BHist}, LinearMapSingletonClassifier f g -> LinearMapSingletonClassifier x y -> LinearMapSingletonClassifier (LinearMapSingletonEval f x) (LinearMapSingletonEval g y)) ∧
      (∀ {f x y : BHist}, LinearMapSingletonCarrier f -> LinearMapSingletonCarrier x -> LinearMapSingletonCarrier y -> LinearMapSingletonClassifier (LinearMapSingletonEval f (append x y)) (append (LinearMapSingletonEval f x) (LinearMapSingletonEval f y))) ∧
      (∀ {r f x : BHist}, LinearMapSingletonCarrier r -> LinearMapSingletonCarrier f -> LinearMapSingletonCarrier x -> LinearMapSingletonClassifier (LinearMapSingletonEval f BHist.Empty) (LinearMapSingletonEval f (LinearMapSingletonEval r x))) ∧
      (∀ {f g x : BHist}, LinearMapSingletonCarrier f -> LinearMapSingletonCarrier g -> LinearMapSingletonCarrier x -> LinearMapSingletonClassifier (LinearMapSingletonEval (LinearMapSingletonComp g f) x) (LinearMapSingletonEval g (LinearMapSingletonEval f x))) := by
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : LinearMapSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
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
            (And.intro sameKR.right.left
              (hsame_trans sameHK.right.right sameKR.right.right))
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
      · intro f x _carrierF _carrierX
        exact emptyCarrier
      · constructor
        · intro f g x y _sameFG _sameXY
          exact emptyClassified
        · constructor
          · intro f x y _carrierF _carrierX _carrierY
            exact emptyClassified
          · constructor
            · intro r f x _carrierR _carrierF _carrierX
              exact emptyClassified
            · intro f g x _carrierF _carrierG _carrierX
              exact emptyClassified

theorem LinearMapSingletonClassifier_append_split_empty_iff {p q h : BHist} :
    LinearMapSingletonClassifier (append p q) h ↔
      LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q ∧
        LinearMapSingletonCarrier h := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    exact ⟨emptyParts.left, emptyParts.right, classified.right.left⟩
  · intro splitData
    have appendCarrier : LinearMapSingletonCarrier (append p q) :=
      append_eq_empty_iff.mpr ⟨splitData.left, splitData.right.left⟩
    exact
      ⟨appendCarrier, splitData.right.right,
        hsame_trans appendCarrier (hsame_symm splitData.right.right)⟩

theorem LinearMapSingletonClassifier_append_visible_left_absurd {p q h : BHist} :
    (LinearMapSingletonClassifier (append p (BHist.e0 q)) h -> False) ∧
      (LinearMapSingletonClassifier (append p (BHist.e1 q)) h -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right

theorem LinearMapSingletonClassifier_append_visible_prefix_absurd {p q h : BHist} :
    (LinearMapSingletonClassifier (append (BHist.e0 p) q) h -> False) ∧
      (LinearMapSingletonClassifier (append (BHist.e1 p) q) h -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.left
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.left

theorem LinearMapSingletonClassifier_append_pair_carrier_iff {p q r s : BHist} :
    LinearMapSingletonClassifier (append p q) (append r s) ↔
      LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q ∧
        LinearMapSingletonCarrier r ∧ LinearMapSingletonCarrier s := by
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact ⟨leftSplit.left, leftSplit.right, rightSplit.left, rightSplit.right⟩
  · intro carriers
    have leftCarrier : LinearMapSingletonCarrier (append p q) :=
      append_eq_empty_iff.mpr ⟨carriers.left, carriers.right.left⟩
    have rightCarrier : LinearMapSingletonCarrier (append r s) :=
      append_eq_empty_iff.mpr ⟨carriers.right.right.left, carriers.right.right.right⟩
    exact
      ⟨leftCarrier, rightCarrier, hsame_trans leftCarrier (hsame_symm rightCarrier)⟩

theorem LinearMapSingletonClassifier_append_pair_empty_iff {p q r s : BHist} :
    LinearMapSingletonClassifier (append p q) (append r s) ↔
      LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q ∧
        LinearMapSingletonCarrier r ∧ LinearMapSingletonCarrier s := by
  constructor
  · intro classified
    have leftEmpty := append_eq_empty_iff.mp classified.left
    have rightEmpty := append_eq_empty_iff.mp classified.right.left
    exact ⟨leftEmpty.left, leftEmpty.right, rightEmpty.left, rightEmpty.right⟩
  · intro splitData
    have leftCarrier : LinearMapSingletonCarrier (append p q) :=
      append_eq_empty_iff.mpr ⟨splitData.left, splitData.right.left⟩
    have rightCarrier : LinearMapSingletonCarrier (append r s) :=
      append_eq_empty_iff.mpr ⟨splitData.right.right.left, splitData.right.right.right⟩
    exact
      ⟨leftCarrier, rightCarrier,
        hsame_trans leftCarrier (hsame_symm rightCarrier)⟩

theorem LinearMapSingletonClassifier_continuation_closed {P P' Q Q' left right : BHist} :
    LinearMapSingletonClassifier P P' -> LinearMapSingletonClassifier Q Q' -> Cont P Q left ->
      Cont P' Q' right -> LinearMapSingletonClassifier left right := by
  intro classifiedP classifiedQ leftContinuation rightContinuation
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame classifiedP.left classifiedQ.left leftContinuation
      (cont_right_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame classifiedP.right.left classifiedQ.right.left rightContinuation
      (cont_right_unit BHist.Empty)
  exact And.intro leftEmpty
    (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem LinearMapSingletonClassifier_continuation_left_closed {P P' Q left : BHist} :
    LinearMapSingletonClassifier P P' -> LinearMapSingletonCarrier Q -> Cont P Q left ->
      LinearMapSingletonCarrier left ∧ LinearMapSingletonClassifier left BHist.Empty := by
  intro classifiedP carrierQ leftContinuation
  have leftEmpty : LinearMapSingletonCarrier left :=
    cont_respects_hsame classifiedP.left carrierQ leftContinuation (cont_right_unit BHist.Empty)
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact And.intro leftEmpty (And.intro leftEmpty (And.intro emptyCarrier leftEmpty))

theorem LinearMapSingletonClassifier_continuation_pair_factors_iff {p q r s t u : BHist} :
    Cont p q r -> Cont s t u ->
      (LinearMapSingletonClassifier r u ↔
        LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q ∧
          LinearMapSingletonCarrier s ∧ LinearMapSingletonCarrier t) := by
  intro leftContinuation rightContinuation
  cases leftContinuation
  cases rightContinuation
  exact LinearMapSingletonClassifier_append_pair_carrier_iff

theorem LinearMapSingletonClassifier_continuation_append_source_classifier_iff {p q r h t : BHist} :
    Cont (append p q) r h ->
      (LinearMapSingletonClassifier h t ↔
        LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q ∧
          LinearMapSingletonCarrier r ∧ LinearMapSingletonCarrier t) := by
  intro continuation
  constructor
  · intro classified
    cases continuation
    have sourceParts := append_eq_empty_iff.mp classified.left
    have prefixParts := append_eq_empty_iff.mp sourceParts.left
    exact And.intro prefixParts.left
      (And.intro prefixParts.right (And.intro sourceParts.right classified.right.left))
  · intro carriers
    cases continuation
    have prefixCarrier : LinearMapSingletonCarrier (append p q) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carriers.right.left)
    have sourceCarrier : LinearMapSingletonCarrier (append (append p q) r) :=
      append_eq_empty_iff.mpr (And.intro prefixCarrier carriers.right.right.left)
    exact
      And.intro sourceCarrier
        (And.intro carriers.right.right.right
          (hsame_trans sourceCarrier (hsame_symm carriers.right.right.right)))

theorem LinearMapSingletonClassifier_continuation_append_target_classifier_iff {p q r h t : BHist} :
    Cont p (append q r) h ->
      (LinearMapSingletonClassifier h t ↔
        LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q ∧
          LinearMapSingletonCarrier r ∧ LinearMapSingletonCarrier t) := by
  intro continuation
  constructor
  · intro classified
    cases continuation
    have sourceParts := append_eq_empty_iff.mp classified.left
    have targetParts := append_eq_empty_iff.mp sourceParts.right
    exact And.intro sourceParts.left
      (And.intro targetParts.left (And.intro targetParts.right classified.right.left))
  · intro carriers
    cases continuation
    have targetCarrier : LinearMapSingletonCarrier (append q r) :=
      append_eq_empty_iff.mpr (And.intro carriers.right.left carriers.right.right.left)
    have sourceCarrier : LinearMapSingletonCarrier (append p (append q r)) :=
      append_eq_empty_iff.mpr (And.intro carriers.left targetCarrier)
    exact
      And.intro sourceCarrier
        (And.intro carriers.right.right.right
          (hsame_trans sourceCarrier (hsame_symm carriers.right.right.right)))

theorem LinearMapSingletonClassifier_continuation_right_closed {P Q Q' right : BHist} :
    LinearMapSingletonCarrier P -> LinearMapSingletonClassifier Q Q' -> Cont P Q right ->
      LinearMapSingletonCarrier right ∧ LinearMapSingletonClassifier right BHist.Empty := by
  intro carrierP classifiedQ rightContinuation
  have rightEmpty : LinearMapSingletonCarrier right :=
    cont_respects_hsame carrierP classifiedQ.left rightContinuation (cont_right_unit BHist.Empty)
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact And.intro rightEmpty (And.intro rightEmpty (And.intro emptyCarrier rightEmpty))

theorem LinearMapSingleton_comp_assoc_empty_classifier {f g h : BHist} :
    LinearMapSingletonCarrier f -> LinearMapSingletonCarrier g -> LinearMapSingletonCarrier h ->
      LinearMapSingletonClassifier (LinearMapSingletonComp h (LinearMapSingletonComp g f))
        BHist.Empty ∧
        LinearMapSingletonClassifier (LinearMapSingletonComp (LinearMapSingletonComp h g) f)
          BHist.Empty ∧
          LinearMapSingletonClassifier (LinearMapSingletonComp h (LinearMapSingletonComp g f))
            (LinearMapSingletonComp (LinearMapSingletonComp h g) f) := by
  intro _carrierF _carrierG _carrierH
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : LinearMapSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  exact And.intro emptyClassifier (And.intro emptyClassifier emptyClassifier)

theorem LinearMapSingletonEval_continuation_classifier_iff {f x y r h : BHist} :
    Cont (LinearMapSingletonEval f x) y r ->
      (LinearMapSingletonClassifier r h ↔
        LinearMapSingletonCarrier y ∧ LinearMapSingletonCarrier h) := by
  intro evalCont
  constructor
  · intro classified
    have rEmpty : hsame r BHist.Empty := classified.left
    have yEmpty : LinearMapSingletonCarrier y :=
      hsame_trans (hsame_symm (append_empty_left y))
        (hsame_trans (hsame_symm evalCont) rEmpty)
    exact And.intro yEmpty classified.right.left
  · intro carriers
    have rEmpty : LinearMapSingletonCarrier r :=
      hsame_trans evalCont (hsame_trans (append_empty_left y) carriers.left)
    exact
      And.intro rEmpty
        (And.intro carriers.right
          (hsame_trans rEmpty (hsame_symm carriers.right)))

theorem LinearMapSingletonEval_comp_continuation_classifier {g f x r : BHist} :
    LinearMapSingletonCarrier g -> LinearMapSingletonCarrier f -> LinearMapSingletonCarrier x ->
      Cont (LinearMapSingletonEval f x) g r ->
        LinearMapSingletonClassifier (LinearMapSingletonEval (LinearMapSingletonComp g f) x) r := by
  intro carrierG _carrierF _carrierX evalCont
  have resultCarrier : LinearMapSingletonCarrier r :=
    cont_respects_hsame (hsame_refl BHist.Empty) carrierG evalCont (cont_right_unit BHist.Empty)
  have carriedResult : LinearMapSingletonClassifier r r :=
    Iff.mpr (LinearMapSingletonEval_continuation_classifier_iff evalCont)
      (And.intro carrierG resultCarrier)
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro carriedResult.right.left (hsame_symm carriedResult.right.left))

theorem LinearMapSingletonEval_context_continuation_classifier_iff {p f x y r h : BHist} :
    Cont (append p (LinearMapSingletonEval f x)) y r ->
      (LinearMapSingletonClassifier r h ↔
        LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier y ∧
          LinearMapSingletonCarrier h) := by
  intro continuation
  constructor
  · intro classified
    have emptyContinuation : Cont (append p (LinearMapSingletonEval f x)) y BHist.Empty :=
      cont_result_hsame_transport continuation classified.left
    have endpoints := cont_empty_result_inversion emptyContinuation
    have contextParts := append_eq_empty_iff.mp endpoints.left
    exact And.intro contextParts.left (And.intro endpoints.right classified.right.left)
  · intro carriers
    have evalCarrier : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
      hsame_refl BHist.Empty
    have contextCarrier : LinearMapSingletonCarrier (append p (LinearMapSingletonEval f x)) :=
      append_eq_empty_iff.mpr (And.intro carriers.left evalCarrier)
    have resultCarrier : LinearMapSingletonCarrier r :=
      cont_respects_hsame contextCarrier carriers.right.left continuation
        (cont_right_unit BHist.Empty)
    exact And.intro resultCarrier
      (And.intro carriers.right.right
        (hsame_trans resultCarrier (hsame_symm carriers.right.right)))

theorem LinearMapSingletonEval_context_continuation_visible_context_absurd
    {p f x y r h : BHist} :
    (Cont (append (BHist.e0 p) (LinearMapSingletonEval f x)) y r ->
      LinearMapSingletonClassifier r h -> False) ∧
      (Cont (append (BHist.e1 p) (LinearMapSingletonEval f x)) y r ->
        LinearMapSingletonClassifier r h -> False) := by
  exact And.intro
    (fun continuation classified =>
      not_hsame_e0_empty ((LinearMapSingletonEval_context_continuation_classifier_iff
        continuation).mp classified).left)
    (fun continuation classified =>
      not_hsame_e1_empty ((LinearMapSingletonEval_context_continuation_classifier_iff
        continuation).mp classified).left)

theorem LinearMapSingletonEval_continuation_visible_target_classifier_absurd
    {f x y r p : BHist} :
    Cont (LinearMapSingletonEval f x) y r ->
      (LinearMapSingletonClassifier r (BHist.e0 p) -> False) ∧
        (LinearMapSingletonClassifier r (BHist.e1 p) -> False) := by
  intro evalCont
  constructor
  · intro classified
    have readback := (LinearMapSingletonEval_continuation_classifier_iff evalCont).mp classified
    exact not_hsame_e0_empty readback.right
  · intro classified
    have readback := (LinearMapSingletonEval_continuation_classifier_iff evalCont).mp classified
    exact not_hsame_e1_empty readback.right

theorem LinearMapSingletonEval_continuation_visible_input_classifier_absurd
    {f x p r h : BHist} :
    (Cont (LinearMapSingletonEval f x) (BHist.e0 p) r ->
      LinearMapSingletonClassifier r h -> False) ∧
      (Cont (LinearMapSingletonEval f x) (BHist.e1 p) r ->
        LinearMapSingletonClassifier r h -> False) := by
  constructor
  · intro evalCont classified
    have readback := (LinearMapSingletonEval_continuation_classifier_iff evalCont).mp classified
    exact not_hsame_e0_empty readback.left
  · intro evalCont classified
    have readback := (LinearMapSingletonEval_continuation_classifier_iff evalCont).mp classified
    exact not_hsame_e1_empty readback.left

theorem LinearMapSingletonEval_continuation_visible_input_absurd {f x p r h : BHist} :
    (Cont (LinearMapSingletonEval f x) (BHist.e0 p) r ->
      LinearMapSingletonClassifier r h -> False) ∧
      (Cont (LinearMapSingletonEval f x) (BHist.e1 p) r ->
        LinearMapSingletonClassifier r h -> False) := by
  exact LinearMapSingletonEval_continuation_visible_input_classifier_absurd

theorem LinearMapSingletonEval_continuation_append_target_carrier_iff {f x y p q : BHist} :
    Cont (LinearMapSingletonEval f x) y (append p q) ->
      (LinearMapSingletonCarrier y ↔
        LinearMapSingletonCarrier p ∧ LinearMapSingletonCarrier q) := by
  intro evalCont
  constructor
  · intro carrierY
    have appendCarrier : LinearMapSingletonCarrier (append p q) :=
      hsame_trans evalCont (hsame_trans (append_empty_left y) carrierY)
    exact append_eq_empty_iff.mp appendCarrier
  · intro carriers
    have appendCarrier : LinearMapSingletonCarrier (append p q) :=
      append_eq_empty_iff.mpr carriers
    exact
      hsame_trans (hsame_symm (append_empty_left y))
        (hsame_trans (hsame_symm evalCont) appendCarrier)

theorem LinearMapSingletonEval_continuation_visible_result_absurd {f x y p : BHist} :
    LinearMapSingletonCarrier y ->
      (Cont (LinearMapSingletonEval f x) y (BHist.e0 p) -> False) ∧
        (Cont (LinearMapSingletonEval f x) y (BHist.e1 p) -> False) := by
  intro carrierY
  constructor
  · intro evalCont
    exact not_hsame_e0_empty
      (hsame_trans evalCont (hsame_trans (append_empty_left y) carrierY))
  · intro evalCont
    exact not_hsame_e1_empty
      (hsame_trans evalCont (hsame_trans (append_empty_left y) carrierY))

theorem LinearMapSingletonEval_context_continuation_visible_result_absurd {p f x y z : BHist} :
    LinearMapSingletonCarrier p ->
      LinearMapSingletonCarrier y ->
        (Cont (append p (LinearMapSingletonEval f x)) y (BHist.e0 z) -> False) ∧
          (Cont (append p (LinearMapSingletonEval f x)) y (BHist.e1 z) -> False) := by
  intro carrierP carrierY
  have evalCarrier : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
    hsame_refl BHist.Empty
  have contextCarrier : LinearMapSingletonCarrier (append p (LinearMapSingletonEval f x)) :=
    append_eq_empty_iff.mpr (And.intro carrierP evalCarrier)
  constructor
  · intro continuation
    exact not_hsame_e0_empty
      (cont_respects_hsame contextCarrier carrierY continuation (cont_right_unit BHist.Empty))
  · intro continuation
    exact not_hsame_e1_empty
      (cont_respects_hsame contextCarrier carrierY continuation (cont_right_unit BHist.Empty))

theorem LinearMapSingletonEval_visible_target_classifier_absurd {f x p : BHist} :
    (LinearMapSingletonClassifier (LinearMapSingletonEval f x) (BHist.e0 p) -> False) ∧
      (LinearMapSingletonClassifier (LinearMapSingletonEval f x) (BHist.e1 p) -> False) := by
  constructor
  · intro classified
    exact not_hsame_e0_empty classified.right.left
  · intro classified
    exact not_hsame_e1_empty classified.right.left

end BEDC.Derived.LinearMapUp
