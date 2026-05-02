import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def FpsSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def FpsSingletonClassifier (h k : BHist) : Prop :=
  FpsSingletonCarrier h ∧ FpsSingletonCarrier k ∧ hsame h k

def FpsSingletonZero : BHist :=
  BHist.Empty

def FpsSingletonOne : BHist :=
  BHist.Empty

def FpsSingletonCoeff (_F _n : BHist) : BHist :=
  BHist.Empty

def FpsSingletonAdd (_F _G : BHist) : BHist :=
  BHist.Empty

def FpsSingletonMul (_F _G : BHist) : BHist :=
  BHist.Empty

theorem fps_singleton_empty_schema_laws :
    SemanticNameCert FpsSingletonCarrier FpsSingletonCarrier FpsSingletonCarrier
      FpsSingletonClassifier ∧
      FpsSingletonCarrier FpsSingletonZero ∧
      FpsSingletonCarrier FpsSingletonOne ∧
      (forall F n : BHist, FpsSingletonCarrier (FpsSingletonCoeff F n)) ∧
      (forall {F G : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
        FpsSingletonCarrier (FpsSingletonAdd F G) ∧
          FpsSingletonCarrier (FpsSingletonMul F G)) ∧
      (forall {F G F' G' : BHist}, FpsSingletonClassifier F F' ->
        FpsSingletonClassifier G G' ->
          FpsSingletonClassifier (FpsSingletonAdd F G) (FpsSingletonAdd F' G') ∧
            FpsSingletonClassifier (FpsSingletonMul F G) (FpsSingletonMul F' G')) := by
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : FpsSingletonClassifier BHist.Empty BHist.Empty :=
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
      · exact emptyCarrier
      · constructor
        · intro F n
          exact emptyCarrier
        · constructor
          · intro F G _carrierF _carrierG
            exact And.intro emptyCarrier emptyCarrier
          · intro F G F' G' _sameF _sameG
            exact And.intro emptyClassified emptyClassified

def FpsSingletonEmptyHistoryCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def FpsSingletonEmptyHistoryClassifier (h k : BHist) : Prop :=
  FpsSingletonEmptyHistoryCarrier h ∧ FpsSingletonEmptyHistoryCarrier k ∧ hsame h k

theorem FpsSingletonEmptyHistory_semanticNameCert :
    SemanticNameCert FpsSingletonEmptyHistoryCarrier FpsSingletonEmptyHistoryCarrier
      FpsSingletonEmptyHistoryCarrier FpsSingletonEmptyHistoryClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
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

end BEDC.Derived.FpsUp
