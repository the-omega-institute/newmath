import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

def FieldExtSingletonCarrier (h : BHist) : Prop :=
  FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h

def FieldExtSingletonClassifier (h k : BHist) : Prop :=
  FieldSingletonClassifier h k ∧ VecSpaceSingletonClassifier h k

theorem FieldExtSingleton_embedding_obligations :
    SemanticNameCert FieldExtSingletonCarrier FieldExtSingletonCarrier
        FieldExtSingletonCarrier FieldExtSingletonClassifier ∧
      (forall {h k : BHist}, FieldExtSingletonClassifier h k ->
        FieldSingletonClassifier h k ∧ VecSpaceSingletonClassifier h k) ∧
      (forall {h k : BHist}, FieldSingletonClassifier h k -> VecSpaceSingletonClassifier h k ->
        FieldExtSingletonClassifier h k) := by
  have emptyCarrier : FieldExtSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  have semantic :
      SemanticNameCert FieldExtSingletonCarrier FieldExtSingletonCarrier
        FieldExtSingletonCarrier FieldExtSingletonClassifier := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro
          (And.intro carrier.left (And.intro carrier.left (hsame_refl h)))
          (And.intro carrier.right (And.intro carrier.right (hsame_refl h)))
      equiv_symm := by
        intro h k same
        exact And.intro
          (And.intro same.left.right.left
            (And.intro same.left.left (hsame_symm same.left.right.right)))
          (And.intro same.right.right.left
            (And.intro same.right.left (hsame_symm same.right.right.right)))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro
          (And.intro sameHK.left.left
            (And.intro sameKR.left.right.left
              (hsame_trans sameHK.left.right.right sameKR.left.right.right)))
          (And.intro sameHK.right.left
            (And.intro sameKR.right.right.left
              (hsame_trans sameHK.right.right.right sameKR.right.right.right)))
      carrier_respects_equiv := by
        intro _h _k same _carrier
        exact And.intro same.left.right.left same.right.right.left
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }
  exact And.intro semantic
    (And.intro
      (by
        intro h k classified
        exact classified)
      (by
        intro h k fieldClassified vecClassified
        exact And.intro fieldClassified vecClassified))

end BEDC.Derived.FieldExtUp
