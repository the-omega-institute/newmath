import BEDC.Derived.PartialBellUp

namespace BEDC.Derived.BellPolynomialUp

-- 权重函数读取 $x_1,x_2,\ldots$；第 $i$ 个块大小使用 `weights i`。
def partialBellPolynomial (weights : Nat -> Nat) (n k : Nat) : Nat :=
  BEDC.Derived.PartialBellUp.partialBell weights n k

def completeBellPolynomialPrefix (weights : Nat -> Nat) (n : Nat) (k : Nat) : Nat :=
  BEDC.Derived.PartialBellUp.completeBellPrefix weights n k

def completeBellPolynomial (weights : Nat -> Nat) (n : Nat) : Nat :=
  BEDC.Derived.PartialBellUp.completeBell weights n

-- Faà di Bruno 的系数槽在本有限导出中只记录部分 Bell 多项式系数。
def faaDiBrunoFormalCoefficient (weights : Nat -> Nat) (n k : Nat) : Nat :=
  partialBellPolynomial weights n k

def bellPolynomialTerms (n k : Nat) : List BEDC.Derived.PartialBellUp.PartialBellTerm :=
  BEDC.Derived.PartialBellUp.partialBellTerms n k

theorem partialBellPolynomial_zero_zero (weights : Nat -> Nat) :
    partialBellPolynomial weights 0 0 = 1 := by
  exact BEDC.Derived.PartialBellUp.partialBell_zero_zero weights

theorem partialBellPolynomial_zero_succ (weights : Nat -> Nat) (k : Nat) :
    partialBellPolynomial weights 0 (Nat.succ k) = 0 := by
  exact BEDC.Derived.PartialBellUp.partialBell_zero_succ weights k

theorem partialBellPolynomial_succ_zero (weights : Nat -> Nat) (n : Nat) :
    partialBellPolynomial weights (Nat.succ n) 0 = 0 := by
  exact BEDC.Derived.PartialBellUp.partialBell_succ_zero weights n

theorem partialBellPolynomial_recurrence (weights : Nat -> Nat) (n k : Nat) :
    partialBellPolynomial weights (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.PartialBellUp.termsEval weights
          (BEDC.Derived.PartialBellUp.singletonTerms
            (BEDC.Derived.PartialBellUp.partialBellTerms n k)) +
        BEDC.Derived.PartialBellUp.termsEval weights
          (BEDC.Derived.PartialBellUp.growTerms
            (BEDC.Derived.PartialBellUp.partialBellTerms n (Nat.succ k))) := by
  exact BEDC.Derived.PartialBellUp.partialBell_succ_succ_recurrence weights n k

theorem partialBellPolynomial_allOnes_stirlingSecond (n k : Nat) :
    partialBellPolynomial (fun _ => 1) n k =
      BEDC.Derived.StirlingUp.stirlingSecond n k := by
  exact BEDC.Derived.PartialBellUp.partialBell_allOnes_stirlingSecond n k

theorem partialBellPolynomial_allOnes_recurrence (n k : Nat) :
    partialBellPolynomial (fun _ => 1) (Nat.succ n) (Nat.succ k) =
      Nat.succ k * partialBellPolynomial (fun _ => 1) n (Nat.succ k) +
        partialBellPolynomial (fun _ => 1) n k := by
  rw [partialBellPolynomial_allOnes_stirlingSecond]
  rw [partialBellPolynomial_allOnes_stirlingSecond]
  rw [partialBellPolynomial_allOnes_stirlingSecond]
  exact BEDC.Derived.StirlingUp.stirlingSecond_recurrence n k

theorem completeBellPolynomial_prefix_allOnes_bellPrefix (n k : Nat) :
    completeBellPolynomialPrefix (fun _ => 1) n k =
      BEDC.Derived.BellNumberUp.bellStirlingPrefix n k := by
  exact BEDC.Derived.PartialBellUp.completeBellPrefix_allOnes_bellPrefix n k

theorem completeBellPolynomial_allOnes_bellNumber (n : Nat) :
    completeBellPolynomial (fun _ => 1) n =
      BEDC.Derived.BellNumberUp.bellNumber n := by
  exact BEDC.Derived.PartialBellUp.partialBell_completeBell n

theorem completeBellPolynomial_allOnes_StirlingUp_bellNumber (n : Nat) :
    completeBellPolynomial (fun _ => 1) n =
      BEDC.Derived.StirlingUp.bellNumber n := by
  rw [completeBellPolynomial_allOnes_bellNumber n]
  exact BEDC.Derived.BellNumberUp.bellNumber_matches_StirlingUp n

theorem faaDiBrunoFormalCoefficient_partialBellPolynomial
    (weights : Nat -> Nat) (n k : Nat) :
    faaDiBrunoFormalCoefficient weights n k =
      partialBellPolynomial weights n k := by
  rfl

theorem faaDiBrunoFormalCoefficient_allOnes_stirlingSecond (n k : Nat) :
    faaDiBrunoFormalCoefficient (fun _ => 1) n k =
      BEDC.Derived.StirlingUp.stirlingSecond n k := by
  exact partialBellPolynomial_allOnes_stirlingSecond n k

theorem BellPolynomialUp_constructive_export :
    (forall weights : Nat -> Nat, partialBellPolynomial weights 0 0 = 1) /\
      (forall weights : Nat -> Nat, forall n k : Nat,
        partialBellPolynomial weights (Nat.succ n) (Nat.succ k) =
          BEDC.Derived.PartialBellUp.termsEval weights
              (BEDC.Derived.PartialBellUp.singletonTerms
                (BEDC.Derived.PartialBellUp.partialBellTerms n k)) +
            BEDC.Derived.PartialBellUp.termsEval weights
              (BEDC.Derived.PartialBellUp.growTerms
                (BEDC.Derived.PartialBellUp.partialBellTerms n (Nat.succ k)))) /\
      (forall n : Nat,
        completeBellPolynomial (fun _ => 1) n =
          BEDC.Derived.BellNumberUp.bellNumber n) /\
      (forall weights : Nat -> Nat, forall n k : Nat,
        faaDiBrunoFormalCoefficient weights n k =
          partialBellPolynomial weights n k) := by
  constructor
  · intro weights
    exact partialBellPolynomial_zero_zero weights
  · constructor
    · intro weights n k
      exact partialBellPolynomial_recurrence weights n k
    · constructor
      · intro n
        exact completeBellPolynomial_allOnes_bellNumber n
      · intro weights n k
        exact faaDiBrunoFormalCoefficient_partialBellPolynomial weights n k

end BEDC.Derived.BellPolynomialUp
