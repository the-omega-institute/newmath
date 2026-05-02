import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def fieldSingletonEmptyCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def fieldSingletonEmptyClassifier (h k : BHist) : Prop :=
  fieldSingletonEmptyCarrier h ∧ fieldSingletonEmptyCarrier k ∧ hsame h k

def fieldSingletonEmptyNonZero (h : BHist) : Prop :=
  fieldSingletonEmptyClassifier h BHist.Empty -> False

def fieldSingletonEmptyMul (_x _y : BHist) : BHist :=
  BHist.Empty

theorem fieldSingletonEmptyClassifier_mul_empty_endpoint_iff {h k out : BHist} :
    fieldSingletonEmptyClassifier (fieldSingletonEmptyMul h k) out ↔ hsame out BHist.Empty := by
  constructor
  · intro classified
    exact classified.right.left
  · intro outEmpty
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro outEmpty (hsame_symm outEmpty))

def fieldSingletonEmptyOne : BHist :=
  BHist.Empty

def fieldSingletonEmptyInv (_h : BHist) (_p : fieldSingletonEmptyNonZero _h) : BHist :=
  BHist.Empty

theorem fieldSingletonEmptyNonZero_empty_endpoint_absurd {h : BHist} :
    hsame h BHist.Empty -> fieldSingletonEmptyNonZero h -> False := by
  intro sameEmpty nonzero
  apply nonzero
  exact And.intro sameEmpty
    (And.intro (hsame_refl BHist.Empty) sameEmpty)

theorem fieldSingletonEmptyCarrier_semanticNameCert :
    SemanticNameCert fieldSingletonEmptyCarrier fieldSingletonEmptyCarrier
      fieldSingletonEmptyCarrier fieldSingletonEmptyClassifier := by
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
          (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
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

theorem field_singleton_empty_schema_laws :
    (fieldSingletonEmptyCarrier BHist.Empty) ∧
      (fieldSingletonEmptyNonZero BHist.Empty -> False) ∧
      (∀ {h k : BHist}, fieldSingletonEmptyClassifier h k ->
        fieldSingletonEmptyNonZero h -> fieldSingletonEmptyNonZero k) ∧
      (∀ (h : BHist) (p : fieldSingletonEmptyNonZero h), fieldSingletonEmptyCarrier h ->
        fieldSingletonEmptyCarrier (fieldSingletonEmptyInv h p)) ∧
      (∀ (h : BHist) (p : fieldSingletonEmptyNonZero h),
        fieldSingletonEmptyClassifier (fieldSingletonEmptyMul (fieldSingletonEmptyInv h p) h)
          fieldSingletonEmptyOne) ∧
      (∀ (h : BHist) (p : fieldSingletonEmptyNonZero h),
        fieldSingletonEmptyClassifier (fieldSingletonEmptyMul h (fieldSingletonEmptyInv h p))
          fieldSingletonEmptyOne) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro nonzeroEmpty
      apply nonzeroEmpty
      constructor
      · exact hsame_refl BHist.Empty
      · constructor
        · exact hsame_refl BHist.Empty
        · exact hsame_refl BHist.Empty
    · constructor
      · intro h k sameHK nonzeroH
        intro sameKEmpty
        apply nonzeroH
        constructor
        · exact sameHK.left
        · constructor
          · exact hsame_refl BHist.Empty
          · exact hsame_trans sameHK.right.right sameKEmpty.right.right
      · constructor
        · intro h p carrierH
          exact hsame_refl BHist.Empty
        · constructor
          · intro h p
            constructor
            · exact hsame_refl BHist.Empty
            · constructor
              · exact hsame_refl BHist.Empty
              · exact hsame_refl BHist.Empty
          · intro h p
            constructor
            · exact hsame_refl BHist.Empty
            · constructor
              · exact hsame_refl BHist.Empty
              · exact hsame_refl BHist.Empty

end BEDC.Derived.FieldUp
