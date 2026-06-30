import BEDC.Derived.BellPolynomialUp

namespace BEDC.Derived.FaaDiBrunoUp

abbrev PartialBellTerm :=
  BEDC.Derived.PartialBellUp.PartialBellTerm

def partialBellTerms (n k : Nat) : List PartialBellTerm :=
  BEDC.Derived.PartialBellUp.partialBellTerms n k

def partialBellPolynomial (weights : Nat -> Nat) (n k : Nat) : Nat :=
  BEDC.Derived.BellPolynomialUp.partialBellPolynomial weights n k

def completeBellPolynomialPrefix (weights : Nat -> Nat) (n : Nat) (k : Nat) : Nat :=
  BEDC.Derived.BellPolynomialUp.completeBellPolynomialPrefix weights n k

def completeBellPolynomial (weights : Nat -> Nat) (n : Nat) : Nat :=
  BEDC.Derived.BellPolynomialUp.completeBellPolynomial weights n

def faaDiBrunoFormalCoefficient (weights : Nat -> Nat) (n k : Nat) : Nat :=
  partialBellPolynomial weights n k

structure FormalDerivativeJet where
  outerDerivativeAtInner : Nat -> Nat
  innerDerivative : Nat -> Nat

def faaDiBrunoTerm (jet : FormalDerivativeJet) (n k : Nat) : Nat :=
  jet.outerDerivativeAtInner k * partialBellPolynomial jet.innerDerivative n k

def faaDiBrunoRhsPrefix (jet : FormalDerivativeJet) (n : Nat) : Nat -> Nat
  | 0 => faaDiBrunoTerm jet n 0
  | Nat.succ k => faaDiBrunoRhsPrefix jet n k + faaDiBrunoTerm jet n (Nat.succ k)

def faaDiBrunoRhs (jet : FormalDerivativeJet) (n : Nat) : Nat :=
  faaDiBrunoRhsPrefix jet n n

def faaDiBrunoFormalRhs
    (outerDerivativeAtInner innerDerivative : Nat -> Nat) (n : Nat) : Nat :=
  faaDiBrunoRhs
    { outerDerivativeAtInner := outerDerivativeAtInner,
      innerDerivative := innerDerivative }
    n

def faaDiBrunoFormalFormula
    (compositeDerivative : Nat)
    (outerDerivativeAtInner innerDerivative : Nat -> Nat)
    (n : Nat) : Prop :=
  compositeDerivative =
    faaDiBrunoFormalRhs outerDerivativeAtInner innerDerivative n

theorem partialBellPolynomial_zero_zero (weights : Nat -> Nat) :
    partialBellPolynomial weights 0 0 = 1 := by
  exact BEDC.Derived.BellPolynomialUp.partialBellPolynomial_zero_zero weights

theorem partialBellPolynomial_zero_succ (weights : Nat -> Nat) (k : Nat) :
    partialBellPolynomial weights 0 (Nat.succ k) = 0 := by
  exact BEDC.Derived.BellPolynomialUp.partialBellPolynomial_zero_succ weights k

theorem partialBellPolynomial_succ_zero (weights : Nat -> Nat) (n : Nat) :
    partialBellPolynomial weights (Nat.succ n) 0 = 0 := by
  exact BEDC.Derived.BellPolynomialUp.partialBellPolynomial_succ_zero weights n

theorem partialBellPolynomial_recurrence (weights : Nat -> Nat) (n k : Nat) :
    partialBellPolynomial weights (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.PartialBellUp.termsEval weights
          (BEDC.Derived.PartialBellUp.singletonTerms (partialBellTerms n k)) +
        BEDC.Derived.PartialBellUp.termsEval weights
          (BEDC.Derived.PartialBellUp.growTerms
            (partialBellTerms n (Nat.succ k))) := by
  exact BEDC.Derived.BellPolynomialUp.partialBellPolynomial_recurrence weights n k

theorem partialBellPolynomial_allOnes_stirlingSecond (n k : Nat) :
    partialBellPolynomial (fun _ => 1) n k =
      BEDC.Derived.StirlingUp.stirlingSecond n k := by
  exact BEDC.Derived.BellPolynomialUp.partialBellPolynomial_allOnes_stirlingSecond n k

theorem partialBellPolynomial_allOnes_recurrence (n k : Nat) :
    partialBellPolynomial (fun _ => 1) (Nat.succ n) (Nat.succ k) =
      Nat.succ k * partialBellPolynomial (fun _ => 1) n (Nat.succ k) +
        partialBellPolynomial (fun _ => 1) n k := by
  exact BEDC.Derived.BellPolynomialUp.partialBellPolynomial_allOnes_recurrence n k

theorem completeBellPolynomialPrefix_zero (weights : Nat -> Nat) (n : Nat) :
    completeBellPolynomialPrefix weights n 0 =
      partialBellPolynomial weights n 0 := by
  rfl

theorem completeBellPolynomialPrefix_succ
    (weights : Nat -> Nat) (n k : Nat) :
    completeBellPolynomialPrefix weights n (Nat.succ k) =
      completeBellPolynomialPrefix weights n k +
        partialBellPolynomial weights n (Nat.succ k) := by
  rfl

theorem completeBellPolynomial_definition (weights : Nat -> Nat) (n : Nat) :
    completeBellPolynomial weights n =
      completeBellPolynomialPrefix weights n n := by
  rfl

theorem completeBellPolynomial_allOnes_bellNumber (n : Nat) :
    completeBellPolynomial (fun _ => 1) n =
      BEDC.Derived.BellNumberUp.bellNumber n := by
  exact BEDC.Derived.BellPolynomialUp.completeBellPolynomial_allOnes_bellNumber n

theorem completeBellPolynomial_allOnes_StirlingUp_bellNumber (n : Nat) :
    completeBellPolynomial (fun _ => 1) n =
      BEDC.Derived.StirlingUp.bellNumber n := by
  exact
    BEDC.Derived.BellPolynomialUp.completeBellPolynomial_allOnes_StirlingUp_bellNumber n

theorem faaDiBrunoFormalCoefficient_partialBellPolynomial
    (weights : Nat -> Nat) (n k : Nat) :
    faaDiBrunoFormalCoefficient weights n k =
      partialBellPolynomial weights n k := by
  rfl

theorem faaDiBrunoFormalCoefficient_allOnes_stirlingSecond (n k : Nat) :
    faaDiBrunoFormalCoefficient (fun _ => 1) n k =
      BEDC.Derived.StirlingUp.stirlingSecond n k := by
  exact partialBellPolynomial_allOnes_stirlingSecond n k

theorem faaDiBrunoTerm_definition (jet : FormalDerivativeJet) (n k : Nat) :
    faaDiBrunoTerm jet n k =
      jet.outerDerivativeAtInner k *
        partialBellPolynomial jet.innerDerivative n k := by
  rfl

theorem faaDiBrunoRhsPrefix_zero (jet : FormalDerivativeJet) (n : Nat) :
    faaDiBrunoRhsPrefix jet n 0 = faaDiBrunoTerm jet n 0 := by
  rfl

theorem faaDiBrunoRhsPrefix_succ
    (jet : FormalDerivativeJet) (n k : Nat) :
    faaDiBrunoRhsPrefix jet n (Nat.succ k) =
      faaDiBrunoRhsPrefix jet n k + faaDiBrunoTerm jet n (Nat.succ k) := by
  rfl

theorem faaDiBrunoRhs_definition (jet : FormalDerivativeJet) (n : Nat) :
    faaDiBrunoRhs jet n = faaDiBrunoRhsPrefix jet n n := by
  rfl

theorem faaDiBrunoFormalRhs_definition
    (outerDerivativeAtInner innerDerivative : Nat -> Nat) (n : Nat) :
    faaDiBrunoFormalRhs outerDerivativeAtInner innerDerivative n =
      faaDiBrunoRhs
        { outerDerivativeAtInner := outerDerivativeAtInner,
          innerDerivative := innerDerivative }
        n := by
  rfl

theorem faaDiBrunoFormalFormula_intro
    (compositeDerivative : Nat)
    (outerDerivativeAtInner innerDerivative : Nat -> Nat)
    (n : Nat)
    (h :
      compositeDerivative =
        faaDiBrunoFormalRhs outerDerivativeAtInner innerDerivative n) :
    faaDiBrunoFormalFormula
      compositeDerivative outerDerivativeAtInner innerDerivative n := by
  exact h

theorem faaDiBrunoFormalFormula_elim
    (compositeDerivative : Nat)
    (outerDerivativeAtInner innerDerivative : Nat -> Nat)
    (n : Nat) :
    faaDiBrunoFormalFormula
        compositeDerivative outerDerivativeAtInner innerDerivative n ->
      compositeDerivative =
        faaDiBrunoFormalRhs outerDerivativeAtInner innerDerivative n := by
  intro h
  exact h

theorem FaaDiBrunoUp_constructive_export :
    (forall weights : Nat -> Nat, partialBellPolynomial weights 0 0 = 1) /\
      (forall weights : Nat -> Nat, forall n k : Nat,
        partialBellPolynomial weights (Nat.succ n) (Nat.succ k) =
          BEDC.Derived.PartialBellUp.termsEval weights
              (BEDC.Derived.PartialBellUp.singletonTerms (partialBellTerms n k)) +
            BEDC.Derived.PartialBellUp.termsEval weights
              (BEDC.Derived.PartialBellUp.growTerms
                (partialBellTerms n (Nat.succ k)))) /\
      (forall n k : Nat,
        partialBellPolynomial (fun _ => 1) n k =
          BEDC.Derived.StirlingUp.stirlingSecond n k) /\
      (forall weights : Nat -> Nat, forall n : Nat,
        completeBellPolynomial weights n =
          completeBellPolynomialPrefix weights n n) /\
      (forall outerDerivativeAtInner innerDerivative : Nat -> Nat,
        forall n : Nat,
          faaDiBrunoFormalRhs outerDerivativeAtInner innerDerivative n =
            faaDiBrunoRhs
              { outerDerivativeAtInner := outerDerivativeAtInner,
                innerDerivative := innerDerivative }
              n) := by
  constructor
  · intro weights
    exact partialBellPolynomial_zero_zero weights
  · constructor
    · intro weights n k
      exact partialBellPolynomial_recurrence weights n k
    · constructor
      · intro n k
        exact partialBellPolynomial_allOnes_stirlingSecond n k
      · constructor
        · intro weights n
          exact completeBellPolynomial_definition weights n
        · intro outerDerivativeAtInner innerDerivative n
          exact faaDiBrunoFormalRhs_definition
            outerDerivativeAtInner innerDerivative n

end BEDC.Derived.FaaDiBrunoUp
