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

theorem LinearMapSingletonEval_visible_target_classifier_absurd {f x p : BHist} :
    (LinearMapSingletonClassifier (LinearMapSingletonEval f x) (BHist.e0 p) -> False) ∧
      (LinearMapSingletonClassifier (LinearMapSingletonEval f x) (BHist.e1 p) -> False) := by
  constructor
  · intro classified
    exact not_hsame_e0_empty classified.right.left
  · intro classified
    exact not_hsame_e1_empty classified.right.left

end BEDC.Derived.LinearMapUp
