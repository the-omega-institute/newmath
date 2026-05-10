import BEDC.Derived.IdealUp
import BEDC.Derived.RingUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.RingUp

theorem IdealUp_concrete_to_schema :
    SemanticNameCert
        (fun h : BHist => RingSingletonCarrier h ∧
          RingSingletonClassifier h RingSingletonZero)
        (fun h : BHist => RingSingletonCarrier h ∧
          RingSingletonClassifier h RingSingletonZero)
        (fun h : BHist => RingSingletonCarrier h ∧
          RingSingletonClassifier h RingSingletonZero)
        RingSingletonClassifier ∧
      (forall {x : BHist}, RingSingletonCarrier x ->
        RingSingletonCarrier x ∧ RingSingletonClassifier x RingSingletonZero) ∧
      (forall {x y : BHist}, RingSingletonCarrier x -> RingSingletonCarrier y ->
        RingSingletonCarrier (RingSingletonAdd x y) ∧
          RingSingletonCarrier (RingSingletonNeg x) ∧
            RingSingletonCarrier (RingSingletonMul x y)) ∧
      (forall {x y : BHist}, RingSingletonCarrier x -> RingSingletonCarrier y ->
        RingSingletonCarrier x ∧ RingSingletonCarrier y ∧
          RingSingletonCarrier (RingSingletonAdd x (RingSingletonNeg y))) := by
  have ringRows := RingSingletonEmptyHistory_laws
  have sourceRows :
      forall {x : BHist}, RingSingletonCarrier x ->
        RingSingletonCarrier x ∧ RingSingletonClassifier x RingSingletonZero := by
    intro x carrierX
    exact And.intro carrierX
      (And.intro carrierX
        (And.intro (hsame_refl RingSingletonZero)
          (hsame_trans carrierX (hsame_symm (hsame_refl RingSingletonZero)))))
  have cert :
      SemanticNameCert
        (fun h : BHist => RingSingletonCarrier h ∧ RingSingletonClassifier h RingSingletonZero)
        (fun h : BHist => RingSingletonCarrier h ∧ RingSingletonClassifier h RingSingletonZero)
        (fun h : BHist => RingSingletonCarrier h ∧ RingSingletonClassifier h RingSingletonZero)
        RingSingletonClassifier := by
    exact {
      core := {
        carrier_inhabited := by
          have zeroCarrier : RingSingletonCarrier RingSingletonZero := hsame_refl RingSingletonZero
          exact Exists.intro RingSingletonZero (sourceRows zeroCarrier)
        equiv_refl := by
          intro h source
          exact And.intro source.left (And.intro source.left (hsame_refl h))
        equiv_symm := by
          intro h k classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro h k r classifiedHK classifiedKR
          exact And.intro classifiedHK.left
            (And.intro classifiedKR.right.left
              (hsame_trans classifiedHK.right.right classifiedKR.right.right))
        carrier_respects_equiv := by
          intro h k classified _sourceH
          exact sourceRows classified.right.left
      }
      pattern_sound := by
        intro _h source
        exact source
      ledger_sound := by
        intro _h source
        exact source
    }
  have operationRows :
      forall {x y : BHist}, RingSingletonCarrier x -> RingSingletonCarrier y ->
        RingSingletonCarrier (RingSingletonAdd x y) ∧
          RingSingletonCarrier (RingSingletonNeg x) ∧
            RingSingletonCarrier (RingSingletonMul x y) := by
    intro x y carrierX carrierY
    have addClassified :
        RingSingletonClassifier (RingSingletonAdd x y) RingSingletonZero :=
      ringRows.right.left carrierX carrierY
    have negClassified :
        RingSingletonClassifier (RingSingletonNeg x) RingSingletonZero :=
      ringRows.right.right.left carrierX
    have mulClassified :
        RingSingletonClassifier (RingSingletonMul x y) RingSingletonZero :=
      ringRows.right.right.right.left carrierX carrierY
    exact And.intro addClassified.left
      (And.intro negClassified.left mulClassified.left)
  have quotientRows :
      forall {x y : BHist}, RingSingletonCarrier x -> RingSingletonCarrier y ->
        RingSingletonCarrier x ∧ RingSingletonCarrier y ∧
          RingSingletonCarrier (RingSingletonAdd x (RingSingletonNeg y)) := by
    intro x y carrierX carrierY
    exact And.intro carrierX
      (And.intro carrierY (operationRows carrierX carrierY).left)
  exact And.intro cert (And.intro sourceRows (And.intro operationRows quotientRows))

end BEDC.Derived.IdealUp
