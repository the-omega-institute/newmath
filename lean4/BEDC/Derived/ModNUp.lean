import BEDC.Derived.RingUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModNUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RingUp

def ModNQuotientCarrier (modulus h : BHist) : Prop :=
  UnaryHistory modulus ∧ RingSingletonCarrier h

def ModNQuotientClassifier (modulus h k : BHist) : Prop :=
  ModNQuotientCarrier modulus h ∧ ModNQuotientCarrier modulus k ∧
    RingSingletonClassifier h k

theorem ModNQuotientClassifier_concrete_rows {modulus : BHist}
    (modulusUnary : UnaryHistory modulus) :
    (forall {h : BHist},
      ModNQuotientCarrier modulus h -> ModNQuotientClassifier modulus h h) ∧
      (forall {h k : BHist},
        ModNQuotientClassifier modulus h k -> ModNQuotientClassifier modulus k h) ∧
      (forall {h k l : BHist},
        ModNQuotientClassifier modulus h k ->
          ModNQuotientClassifier modulus k l -> ModNQuotientClassifier modulus h l) ∧
      (forall {h k : BHist},
        ModNQuotientClassifier modulus h k ->
          ModNQuotientCarrier modulus h -> ModNQuotientCarrier modulus k) := by
  constructor
  · intro h carrierH
    have carrierWithModulus : ModNQuotientCarrier modulus h :=
      And.intro modulusUnary carrierH.right
    exact And.intro carrierWithModulus
      (And.intro carrierWithModulus
        (And.intro carrierWithModulus.right
          (And.intro carrierWithModulus.right (hsame_refl h))))
  · constructor
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left
          (And.intro classified.right.right.right.left
            (And.intro classified.right.right.left
              (hsame_symm classified.right.right.right.right))))
    · constructor
      · intro h k l classifiedHK classifiedKL
        exact And.intro classifiedHK.left
          (And.intro classifiedKL.right.left
            (And.intro classifiedHK.right.right.left
              (And.intro classifiedKL.right.right.right.left
                (hsame_trans classifiedHK.right.right.right.right
                  classifiedKL.right.right.right.right))))
      · intro h k classified _carrierH
        exact classified.right.left

theorem ModNQuotientCarrier_singleton_operation_descent_rows {modulus : BHist}
    (modulusUnary : UnaryHistory modulus) :
    (forall {h k : BHist},
      ModNQuotientCarrier modulus h -> ModNQuotientCarrier modulus k ->
        ModNQuotientCarrier modulus (RingSingletonAdd h k) ∧
          ModNQuotientCarrier modulus (RingSingletonMul h k)) ∧
      (forall {h : BHist},
        ModNQuotientCarrier modulus h -> ModNQuotientCarrier modulus (RingSingletonNeg h)) ∧
      (forall {h h' k k' : BHist},
        ModNQuotientClassifier modulus h h' ->
          ModNQuotientClassifier modulus k k' ->
            ModNQuotientClassifier modulus (RingSingletonAdd h k)
              (RingSingletonAdd h' k') ∧
              ModNQuotientClassifier modulus (RingSingletonMul h k)
                (RingSingletonMul h' k')) ∧
      (forall {h h' : BHist},
        ModNQuotientClassifier modulus h h' ->
          ModNQuotientClassifier modulus (RingSingletonNeg h) (RingSingletonNeg h')) := by
  have emptyRingCarrier : RingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyCarrier : ModNQuotientCarrier modulus BHist.Empty :=
    And.intro modulusUnary emptyRingCarrier
  have emptyClassified : ModNQuotientClassifier modulus BHist.Empty BHist.Empty :=
    And.intro emptyCarrier
      (And.intro emptyCarrier
        (And.intro emptyRingCarrier (And.intro emptyRingCarrier (hsame_refl BHist.Empty))))
  constructor
  · intro h k _carrierH _carrierK
    exact And.intro emptyCarrier emptyCarrier
  · constructor
    · intro h _carrierH
      exact emptyCarrier
    · constructor
      · intro h h' k k' _classifiedHH' _classifiedKK'
        exact And.intro emptyClassified emptyClassified
      · intro h h' _classifiedHH'
        exact emptyClassified

theorem ModN_nz_quotient_certificate {modulus : BHist} :
    UnaryHistory modulus ->
      SemanticNameCert (ModNQuotientCarrier modulus) (ModNQuotientCarrier modulus)
        (ModNQuotientCarrier modulus) (ModNQuotientClassifier modulus) := by
  intro modulusUnary
  have emptyRingCarrier : RingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyCarrier : ModNQuotientCarrier modulus BHist.Empty :=
    And.intro modulusUnary emptyRingCarrier
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrierH
        exact And.intro carrierH
          (And.intro carrierH
            (And.intro carrierH.right
              (And.intro carrierH.right (hsame_refl h))))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left
            (And.intro classified.right.right.right.left
              (And.intro classified.right.right.left
                (hsame_symm classified.right.right.right.right))))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (And.intro classifiedHK.right.right.left
              (And.intro classifiedKR.right.right.right.left
                (hsame_trans classifiedHK.right.right.right.right
                  classifiedKR.right.right.right.right))))
      carrier_respects_equiv := by
        intro h k classified _carrierH
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem ModNQuotient_concrete_namecert_scope {modulus : BHist} :
    UnaryHistory modulus ->
      SemanticNameCert (ModNQuotientCarrier modulus) (ModNQuotientCarrier modulus)
          (ModNQuotientCarrier modulus) (ModNQuotientClassifier modulus) ∧
        (forall {h : BHist}, ModNQuotientCarrier modulus h ->
          ModNQuotientClassifier modulus h h) := by
  intro modulusUnary
  have rows := ModNQuotientClassifier_concrete_rows (modulus := modulus) modulusUnary
  exact And.intro (ModN_nz_quotient_certificate modulusUnary) rows.left

theorem ModNQuotient_singleton_operation_descent_rows {modulus : BHist}
    (modulusUnary : UnaryHistory modulus) :
    (forall {h k : BHist}, ModNQuotientCarrier modulus h -> ModNQuotientCarrier modulus k ->
      ModNQuotientCarrier modulus (RingSingletonAdd h k) ∧
        ModNQuotientCarrier modulus (RingSingletonMul h k)) ∧
    (forall {h : BHist}, ModNQuotientCarrier modulus h ->
      ModNQuotientCarrier modulus (RingSingletonNeg h)) ∧
    (forall {h h' k k' : BHist}, ModNQuotientClassifier modulus h h' ->
      ModNQuotientClassifier modulus k k' ->
        ModNQuotientClassifier modulus (RingSingletonAdd h k) (RingSingletonAdd h' k')) ∧
    (forall {h h' k k' : BHist}, ModNQuotientClassifier modulus h h' ->
      ModNQuotientClassifier modulus k k' ->
        ModNQuotientClassifier modulus (RingSingletonMul h k) (RingSingletonMul h' k')) ∧
    (forall {h h' : BHist}, ModNQuotientClassifier modulus h h' ->
      ModNQuotientClassifier modulus (RingSingletonNeg h) (RingSingletonNeg h')) := by
  have emptyRingCarrier : RingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyCarrier : ModNQuotientCarrier modulus BHist.Empty :=
    And.intro modulusUnary emptyRingCarrier
  have emptyClassifier : ModNQuotientClassifier modulus BHist.Empty BHist.Empty :=
    And.intro emptyCarrier
      (And.intro emptyCarrier
        (And.intro emptyRingCarrier (And.intro emptyRingCarrier (hsame_refl BHist.Empty))))
  constructor
  · intro h k _carrierH _carrierK
    exact And.intro emptyCarrier emptyCarrier
  constructor
  · intro h _carrierH
    exact emptyCarrier
  constructor
  · intro h h' k k' _sameHH' _sameKK'
    exact emptyClassifier
  constructor
  · intro h h' k k' _sameHH' _sameKK'
    exact emptyClassifier
  · intro h h' _sameHH'
    exact emptyClassifier

theorem ModNQuotientSingleton_operation_descent_rows {modulus h h' k k' : BHist} :
    UnaryHistory modulus ->
      (ModNQuotientCarrier modulus h -> ModNQuotientCarrier modulus k ->
        ModNQuotientCarrier modulus (RingSingletonAdd h k) ∧
          ModNQuotientCarrier modulus (RingSingletonMul h k)) ∧
      (ModNQuotientCarrier modulus h ->
        ModNQuotientCarrier modulus (RingSingletonNeg h)) ∧
      (ModNQuotientClassifier modulus h h' -> ModNQuotientClassifier modulus k k' ->
        ModNQuotientClassifier modulus (RingSingletonAdd h k)
          (RingSingletonAdd h' k')) ∧
      (ModNQuotientClassifier modulus h h' -> ModNQuotientClassifier modulus k k' ->
        ModNQuotientClassifier modulus (RingSingletonMul h k)
          (RingSingletonMul h' k')) ∧
      (ModNQuotientClassifier modulus h h' ->
        ModNQuotientClassifier modulus (RingSingletonNeg h) (RingSingletonNeg h')) := by
  intro modulusUnary
  have emptyRingCarrier : RingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyCarrier : ModNQuotientCarrier modulus BHist.Empty :=
    And.intro modulusUnary emptyRingCarrier
  have emptyRingClassifier : RingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyRingCarrier
      (And.intro emptyRingCarrier (hsame_refl BHist.Empty))
  have emptyClassifier : ModNQuotientClassifier modulus BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier emptyRingClassifier)
  constructor
  · intro _carrierH _carrierK
    exact And.intro emptyCarrier emptyCarrier
  · constructor
    · intro _carrierH
      exact emptyCarrier
    · constructor
      · intro _classifiedHH' _classifiedKK'
        exact emptyClassifier
      · constructor
        · intro _classifiedHH' _classifiedKK'
          exact emptyClassifier
        · intro _classifiedHH'
          exact emptyClassifier

end BEDC.Derived.ModNUp
