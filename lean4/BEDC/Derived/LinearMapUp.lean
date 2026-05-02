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

end BEDC.Derived.LinearMapUp
