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
