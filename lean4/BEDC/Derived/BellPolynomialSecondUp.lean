import BEDC.Derived.BellNumberUp
import BEDC.Derived.DobinskiFiniteUp
import BEDC.Derived.PartialBellUp
import BEDC.Derived.TouchardPolyUp

namespace BEDC.Derived.BellPolynomialSecondUp

abbrev stirlingSecond : Nat -> Nat -> Nat :=
  BEDC.Derived.StirlingUp.stirlingSecond

abbrev bellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumber

abbrev partialBellSecond (weights : Nat -> Nat) (n k : Nat) : Nat :=
  BEDC.Derived.PartialBellUp.partialBell weights n k

abbrev completeBellSecondPrefix (weights : Nat -> Nat) (n : Nat) (k : Nat) : Nat :=
  BEDC.Derived.PartialBellUp.completeBellPrefix weights n k

abbrev completeBellSecond (weights : Nat -> Nat) (n : Nat) : Nat :=
  BEDC.Derived.PartialBellUp.completeBell weights n

abbrev natPow : Nat -> Nat -> Nat :=
  BEDC.Derived.TouchardPolyUp.natPow

def phiTerm (n x k : Nat) : Nat :=
  stirlingSecond n k * natPow x k

def phiPrefix (n x : Nat) : Nat -> Nat
  | 0 => phiTerm n x 0
  | Nat.succ k => phiPrefix n x k + phiTerm n x (Nat.succ k)

def phi (n x : Nat) : Nat :=
  phiPrefix n x n

abbrev inclusiveRange : Nat -> List Nat :=
  BEDC.Derived.DobinskiFiniteUp.inclusiveRange

abbrev listNatSum (f : Nat -> Nat) : List Nat -> Nat :=
  BEDC.Derived.DobinskiFiniteUp.listNatSum f

def dobinskiFormalPhi (n x : Nat) : Nat :=
  listNatSum (phiTerm n x) (inclusiveRange n)

def dobinskiFormalBellSupport (n : Nat) : Nat :=
  listNatSum (stirlingSecond n) (inclusiveRange n)

def phiRecurrenceTerm (n x k : Nat) : Nat :=
  (Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k) *
    natPow x k

def phiRecurrencePrefix (n x : Nat) : Nat -> Nat
  | 0 => phiRecurrenceTerm n x 0
  | Nat.succ k => phiRecurrencePrefix n x k + phiRecurrenceTerm n x (Nat.succ k)

def phiRecurrenceRhs (n x : Nat) : Nat :=
  x * phiRecurrencePrefix n x n

theorem natPow_zero (x : Nat) :
    natPow x 0 = 1 := by
  exact BEDC.Derived.TouchardPolyUp.natPow_zero_right x

theorem natPow_succ (x k : Nat) :
    natPow x (Nat.succ k) = x * natPow x k := by
  exact BEDC.Derived.TouchardPolyUp.natPow_succ x k

theorem natPow_one :
    forall k : Nat, natPow 1 k = 1 := by
  exact BEDC.Derived.TouchardPolyUp.natPow_one

theorem partialBellSecond_zero_zero (weights : Nat -> Nat) :
    partialBellSecond weights 0 0 = 1 := by
  exact BEDC.Derived.PartialBellUp.partialBell_zero_zero weights

theorem partialBellSecond_zero_succ (weights : Nat -> Nat) (k : Nat) :
    partialBellSecond weights 0 (Nat.succ k) = 0 := by
  exact BEDC.Derived.PartialBellUp.partialBell_zero_succ weights k

theorem partialBellSecond_succ_zero (weights : Nat -> Nat) (n : Nat) :
    partialBellSecond weights (Nat.succ n) 0 = 0 := by
  exact BEDC.Derived.PartialBellUp.partialBell_succ_zero weights n

theorem partialBellSecond_recurrence (weights : Nat -> Nat) (n k : Nat) :
    partialBellSecond weights (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.PartialBellUp.termsEval weights
          (BEDC.Derived.PartialBellUp.singletonTerms
            (BEDC.Derived.PartialBellUp.partialBellTerms n k)) +
        BEDC.Derived.PartialBellUp.termsEval weights
          (BEDC.Derived.PartialBellUp.growTerms
            (BEDC.Derived.PartialBellUp.partialBellTerms n (Nat.succ k))) := by
  exact BEDC.Derived.PartialBellUp.partialBell_succ_succ_recurrence weights n k

theorem partialBellSecond_allOnes_stirlingSecond (n k : Nat) :
    partialBellSecond (fun _ => 1) n k = stirlingSecond n k := by
  exact BEDC.Derived.PartialBellUp.partialBell_allOnes_stirlingSecond n k

theorem completeBellSecondPrefix_allOnes_bellPrefix (n : Nat) :
    forall k : Nat,
      completeBellSecondPrefix (fun _ => 1) n k =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k := by
  exact BEDC.Derived.PartialBellUp.completeBellPrefix_allOnes_bellPrefix n

theorem completeBellSecond_allOnes_bellNumber (n : Nat) :
    completeBellSecond (fun _ => 1) n = bellNumber n := by
  exact BEDC.Derived.PartialBellUp.partialBell_completeBell n

theorem completeBellSecond_allOnes_StirlingUp_bellNumber (n : Nat) :
    completeBellSecond (fun _ => 1) n =
      BEDC.Derived.StirlingUp.bellNumber n := by
  rw [completeBellSecond_allOnes_bellNumber n]
  exact BEDC.Derived.BellNumberUp.bellNumber_matches_StirlingUp n

theorem phiPrefix_zero (n x : Nat) :
    phiPrefix n x 0 = stirlingSecond n 0 * natPow x 0 := by
  rfl

theorem phiPrefix_succ (n x k : Nat) :
    phiPrefix n x (Nat.succ k) =
      phiPrefix n x k + stirlingSecond n (Nat.succ k) * natPow x (Nat.succ k) := by
  rfl

theorem phi_stirling_prefix (n x : Nat) :
    phi n x = phiPrefix n x n := by
  rfl

theorem phiPrefix_matches_touchardEvalPrefix (n x : Nat) :
    forall k : Nat,
      phiPrefix n x k = BEDC.Derived.TouchardPolyUp.touchardEvalPrefix n x k
  | 0 => by
      rfl
  | Nat.succ k => by
      change phiPrefix n x k + phiTerm n x (Nat.succ k) =
        BEDC.Derived.TouchardPolyUp.touchardEvalPrefix n x k +
          BEDC.Derived.TouchardPolyUp.touchardTerm n x (Nat.succ k)
      rw [phiPrefix_matches_touchardEvalPrefix n x k]
      rfl

theorem phi_eq_touchardEval (n x : Nat) :
    phi n x = BEDC.Derived.TouchardPolyUp.touchardEval n x := by
  unfold phi BEDC.Derived.TouchardPolyUp.touchardEval
  exact phiPrefix_matches_touchardEvalPrefix n x n

theorem phi_one_eq_bellNumber (n : Nat) :
    phi n 1 = bellNumber n := by
  rw [phi_eq_touchardEval n 1]
  exact BEDC.Derived.TouchardPolyUp.touchardEval_one_bellNumber n

theorem phi_one_eq_StirlingUp_bellNumber (n : Nat) :
    phi n 1 = BEDC.Derived.StirlingUp.bellNumber n := by
  rw [phi_one_eq_bellNumber n]
  exact BEDC.Derived.BellNumberUp.bellNumber_matches_StirlingUp n

theorem phiTerm_one (n k : Nat) :
    phiTerm n 1 k = stirlingSecond n k := by
  unfold phiTerm
  rw [natPow_one k]
  exact Nat.mul_one (stirlingSecond n k)

theorem phiPrefix_listNatSum (n x : Nat) :
    forall k : Nat,
      listNatSum (phiTerm n x) (inclusiveRange k) = phiPrefix n x k
  | 0 => by
      rfl
  | Nat.succ k => by
      change
        BEDC.Derived.DobinskiFiniteUp.listNatSum
            (phiTerm n x) (inclusiveRange k ++ [Nat.succ k]) =
          phiPrefix n x k + phiTerm n x (Nat.succ k)
      rw [BEDC.Derived.DobinskiFiniteUp.listNatSum_append]
      rw [show BEDC.Derived.DobinskiFiniteUp.listNatSum
          (phiTerm n x) (inclusiveRange k) = phiPrefix n x k from
        phiPrefix_listNatSum n x k]
      rw [BEDC.Derived.DobinskiFiniteUp.listNatSum_singleton]

theorem dobinskiFormalPhi_eq_phi (n x : Nat) :
    dobinskiFormalPhi n x = phi n x := by
  unfold dobinskiFormalPhi phi
  exact phiPrefix_listNatSum n x n

theorem phi_stirling_list_sum (n x : Nat) :
    phi n x = listNatSum (phiTerm n x) (inclusiveRange n) := by
  exact (dobinskiFormalPhi_eq_phi n x).symm

theorem dobinskiFormalBellSupport_eq_bellNumber (n : Nat) :
    dobinskiFormalBellSupport n = bellNumber n := by
  unfold dobinskiFormalBellSupport bellNumber
  exact (BEDC.Derived.DobinskiFiniteUp.bellNumber_list_stirling_sum n).symm

theorem dobinskiFormalPhi_one_eq_bellSupport (n : Nat) :
    dobinskiFormalPhi n 1 = dobinskiFormalBellSupport n := by
  calc
    dobinskiFormalPhi n 1 = phi n 1 := dobinskiFormalPhi_eq_phi n 1
    _ = bellNumber n := phi_one_eq_bellNumber n
    _ = dobinskiFormalBellSupport n := (dobinskiFormalBellSupport_eq_bellNumber n).symm

theorem phiRecurrencePrefix_zero (n x : Nat) :
    phiRecurrencePrefix n x 0 =
      (1 * stirlingSecond n 1 + stirlingSecond n 0) * natPow x 0 := by
  rfl

theorem phiRecurrencePrefix_succ (n x k : Nat) :
    phiRecurrencePrefix n x (Nat.succ k) =
      phiRecurrencePrefix n x k +
        (Nat.succ (Nat.succ k) * stirlingSecond n (Nat.succ (Nat.succ k)) +
          stirlingSecond n (Nat.succ k)) * natPow x (Nat.succ k) := by
  rfl

theorem phiRecurrencePrefix_matches_touchardStepPrefix (n x : Nat) :
    forall k : Nat,
      phiRecurrencePrefix n x k =
        BEDC.Derived.TouchardPolyUp.touchardStirlingStepPrefix n x k
  | 0 => by
      rfl
  | Nat.succ k => by
      change phiRecurrencePrefix n x k + phiRecurrenceTerm n x (Nat.succ k) =
        BEDC.Derived.TouchardPolyUp.touchardStirlingStepPrefix n x k +
          ((Nat.succ (Nat.succ k) * stirlingSecond n (Nat.succ (Nat.succ k))) +
            stirlingSecond n (Nat.succ k)) * natPow x (Nat.succ k)
      rw [phiRecurrencePrefix_matches_touchardStepPrefix n x k]
      rfl

theorem phi_succ_recurrence (n x : Nat) :
    phi (Nat.succ n) x = phiRecurrenceRhs n x := by
  unfold phiRecurrenceRhs
  rw [phi_eq_touchardEval (Nat.succ n) x]
  rw [BEDC.Derived.TouchardPolyUp.touchardEval_succ_recurrence n x]
  rw [← phiRecurrencePrefix_matches_touchardStepPrefix n x n]

theorem phi_coeff_recurrence (n k : Nat) :
    stirlingSecond (Nat.succ n) (Nat.succ k) =
      Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k := by
  exact BEDC.Derived.StirlingUp.stirlingSecond_recurrence n k

theorem phi_zero (x : Nat) :
    phi 0 x = 1 := by
  rw [phi_eq_touchardEval 0 x]
  exact BEDC.Derived.TouchardPolyUp.touchardEval_zero x

theorem phi_one_degree (x : Nat) :
    phi 1 x = x := by
  unfold phi phiPrefix phiTerm stirlingSecond natPow
  change 0 * 1 + 1 * (x * 1) = x
  rw [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_one]

theorem phi_two_degree (x : Nat) :
    phi 2 x = x + x * x := by
  unfold phi phiPrefix phiTerm stirlingSecond natPow
  change (0 * 1 + 1 * (x * 1)) + 1 * (x * (x * 1)) = x + x * x
  rw [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_one]
  rw [Nat.one_mul]

theorem BellPolynomialSecondUp_constructive_export :
    (forall n k : Nat,
      partialBellSecond (fun _ => 1) n k = stirlingSecond n k) /\
      (forall n : Nat, completeBellSecond (fun _ => 1) n = bellNumber n) /\
      (forall n x : Nat, phi n x = listNatSum (phiTerm n x) (inclusiveRange n)) /\
      (forall n x : Nat, dobinskiFormalPhi n x = phi n x) /\
      (forall n x : Nat, phi (Nat.succ n) x = phiRecurrenceRhs n x) /\
      (forall n : Nat, phi n 1 = BEDC.Derived.StirlingUp.bellNumber n) := by
  constructor
  · intro n k
    exact partialBellSecond_allOnes_stirlingSecond n k
  · constructor
    · intro n
      exact completeBellSecond_allOnes_bellNumber n
    · constructor
      · intro n x
        exact phi_stirling_list_sum n x
      · constructor
        · intro n x
          exact dobinskiFormalPhi_eq_phi n x
        · constructor
          · intro n x
            exact phi_succ_recurrence n x
          · intro n
            exact phi_one_eq_StirlingUp_bellNumber n

end BEDC.Derived.BellPolynomialSecondUp
