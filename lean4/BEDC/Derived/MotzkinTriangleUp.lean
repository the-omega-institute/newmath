import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.IntUp
import BEDC.Derived.MotzkinUp

namespace BEDC.Derived.MotzkinTriangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

/-!
  `motzkinTriangle n k` 计数长度为 `n`、终点高度为 `k` 的 Motzkin 前缀路。
  高度零列给出 Motzkin 数列。
-/
def motzkinTriangle : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, 0 =>
      motzkinTriangle n 0 + motzkinTriangle n 1
  | Nat.succ n, Nat.succ k =>
      motzkinTriangle n k + motzkinTriangle n (Nat.succ k) +
        motzkinTriangle n (Nat.succ (Nat.succ k))

def motzkinNumber (n : Nat) : Nat :=
  motzkinTriangle n 0

def motzkinTrianglePrefix (n : Nat) : Nat -> Nat
  | 0 => motzkinTriangle n 0
  | Nat.succ k => motzkinTrianglePrefix n k + motzkinTriangle n (Nat.succ k)

def motzkinTriangleRowSum (n : Nat) : Nat :=
  motzkinTrianglePrefix n n

def motzkinTriangleFn (n k : BHist) : BHist :=
  natToUnary (motzkinTriangle (bwordLength n) (bwordLength k))

def motzkinNumberFn (n : BHist) : BHist :=
  natToUnary (motzkinNumber (bwordLength n))

def motzkinPrefixRowSumFn (n : BHist) : BHist :=
  natToUnary (motzkinTriangleRowSum (bwordLength n))

theorem motzkinTriangle_zero_zero :
    motzkinTriangle 0 0 = 1 := by
  rfl

theorem motzkinTriangle_zero_succ (k : Nat) :
    motzkinTriangle 0 (Nat.succ k) = 0 := by
  rfl

theorem motzkinTriangle_zero_step (n : Nat) :
    motzkinTriangle (Nat.succ n) 0 =
      motzkinTriangle n 0 + motzkinTriangle n 1 := by
  rfl

theorem motzkinTriangle_recurrence (n k : Nat) :
    motzkinTriangle (Nat.succ n) (Nat.succ k) =
      motzkinTriangle n k + motzkinTriangle n (Nat.succ k) +
        motzkinTriangle n (Nat.succ (Nat.succ k)) := by
  rfl

theorem motzkinTriangle_zero_eq_motzkinNumber (n : Nat) :
    motzkinTriangle n 0 = motzkinNumber n := by
  rfl

theorem motzkinTrianglePrefix_succ (n k : Nat) :
    motzkinTrianglePrefix n (Nat.succ k) =
      motzkinTrianglePrefix n k + motzkinTriangle n (Nat.succ k) := by
  rfl

theorem motzkinTriangleRowSum_prefix (n : Nat) :
    motzkinTriangleRowSum n = motzkinTrianglePrefix n n := by
  rfl

theorem motzkinTriangle_above_row :
    ∀ n extra : Nat, motzkinTriangle n (Nat.succ (n + extra)) = 0
  | 0, _extra => by
      rfl
  | Nat.succ n, extra => by
      change motzkinTriangle n (Nat.succ n + extra) +
          motzkinTriangle n (Nat.succ (Nat.succ n + extra)) +
            motzkinTriangle n (Nat.succ (Nat.succ (Nat.succ n + extra))) = 0
      rw [Nat.succ_add]
      rw [motzkinTriangle_above_row n extra]
      have second := motzkinTriangle_above_row n (Nat.succ extra)
      rw [Nat.add_succ] at second
      rw [second]
      have third := motzkinTriangle_above_row n (Nat.succ (Nat.succ extra))
      rw [Nat.add_succ] at third
      rw [Nat.add_succ] at third
      rw [third]

theorem motzkinTriangle_row_boundary (n : Nat) :
    motzkinTriangle n (Nat.succ n) = 0 := by
  have boundary := motzkinTriangle_above_row n 0
  rw [Nat.add_zero] at boundary
  exact boundary

theorem motzkinTriangle_small_zero_column :
    motzkinNumber 0 = 1 ∧ motzkinNumber 1 = 1 ∧
      motzkinNumber 2 = 2 ∧ motzkinNumber 3 = 4 ∧
        motzkinNumber 4 = 9 ∧ motzkinNumber 5 = 21 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

theorem motzkinTriangleRowSum_zero :
    motzkinTriangleRowSum 0 = 1 := by
  rfl

theorem motzkinTriangleRowSum_one :
    motzkinTriangleRowSum 1 = 2 := by
  rfl

theorem motzkinTriangleRowSum_two :
    motzkinTriangleRowSum 2 = 5 := by
  rfl

theorem motzkinTriangleRowSum_three :
    motzkinTriangleRowSum 3 = 13 := by
  rfl

theorem motzkinPrefixRowSum_export :
    motzkinTriangleRowSum 0 = 1 ∧ motzkinTriangleRowSum 1 = 2 ∧
      motzkinTriangleRowSum 2 = 5 ∧ motzkinTriangleRowSum 3 = 13 ∧
        ∀ n : Nat, motzkinTriangleRowSum n = motzkinTrianglePrefix n n := by
  constructor
  · exact motzkinTriangleRowSum_zero
  · constructor
    · exact motzkinTriangleRowSum_one
    · constructor
      · exact motzkinTriangleRowSum_two
      · constructor
        · exact motzkinTriangleRowSum_three
        · intro n
          exact motzkinTriangleRowSum_prefix n

theorem motzkinTriangleFn_unary_result (n k : BHist) :
    UnaryHistory (motzkinTriangleFn n k) := by
  unfold motzkinTriangleFn
  exact natToUnary_unary _

theorem motzkinNumberFn_unary_result (n : BHist) :
    UnaryHistory (motzkinNumberFn n) := by
  unfold motzkinNumberFn
  exact natToUnary_unary _

theorem motzkinPrefixRowSumFn_unary_result (n : BHist) :
    UnaryHistory (motzkinPrefixRowSumFn n) := by
  unfold motzkinPrefixRowSumFn
  exact natToUnary_unary _

theorem motzkinTriangleFn_recurrence_natToUnary (n k : Nat) :
    motzkinTriangleFn (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        (motzkinTriangle n k + motzkinTriangle n (Nat.succ k) +
          motzkinTriangle n (Nat.succ (Nat.succ k))) := by
  unfold motzkinTriangleFn
  rw [natToUnary_length, natToUnary_length]
  rfl

theorem motzkinTriangleFn_zero_eq_motzkinNumberFn (n : Nat) :
    motzkinTriangleFn (natToUnary n) BHist.Empty = motzkinNumberFn (natToUnary n) := by
  unfold motzkinTriangleFn motzkinNumberFn motzkinNumber
  rw [natToUnary_length]
  rfl

theorem motzkinTriangle_matches_MotzkinUp_small :
    BEDC.Derived.MotzkinUp.Motzkin (natToUnary 0) (natToUnary (motzkinNumber 0)) ∧
      BEDC.Derived.MotzkinUp.Motzkin (natToUnary 1) (natToUnary (motzkinNumber 1)) ∧
        BEDC.Derived.MotzkinUp.Motzkin (natToUnary 2) (natToUnary (motzkinNumber 2)) ∧
          BEDC.Derived.MotzkinUp.Motzkin (natToUnary 3) (natToUnary (motzkinNumber 3)) ∧
            BEDC.Derived.MotzkinUp.Motzkin (natToUnary 4) (natToUnary (motzkinNumber 4)) ∧
              BEDC.Derived.MotzkinUp.Motzkin
                (natToUnary 5) (natToUnary (motzkinNumber 5)) := by
  change
    BEDC.Derived.MotzkinUp.Motzkin BHist.Empty (natToUnary 1) ∧
      BEDC.Derived.MotzkinUp.Motzkin (natToUnary 1) (natToUnary 1) ∧
        BEDC.Derived.MotzkinUp.Motzkin (natToUnary 2) (natToUnary 2) ∧
          BEDC.Derived.MotzkinUp.Motzkin (natToUnary 3) (natToUnary 4) ∧
            BEDC.Derived.MotzkinUp.Motzkin (natToUnary 4) (natToUnary 9) ∧
              BEDC.Derived.MotzkinUp.Motzkin (natToUnary 5) (natToUnary 21)
  exact BEDC.Derived.MotzkinUp.motzkin_small_values

theorem MotzkinTriangleUp_constructive_export :
    motzkinTriangle 0 0 = 1 ∧
      (∀ n : Nat, motzkinTriangle (Nat.succ n) 0 =
        motzkinTriangle n 0 + motzkinTriangle n 1) ∧
      (∀ n k : Nat, motzkinTriangle (Nat.succ n) (Nat.succ k) =
        motzkinTriangle n k + motzkinTriangle n (Nat.succ k) +
          motzkinTriangle n (Nat.succ (Nat.succ k))) ∧
      (∀ n : Nat, motzkinTriangle n 0 = motzkinNumber n) ∧
      (∀ n : Nat, motzkinTriangleRowSum n = motzkinTrianglePrefix n n) ∧
      (motzkinTriangleRowSum 0 = 1 ∧ motzkinTriangleRowSum 1 = 2 ∧
        motzkinTriangleRowSum 2 = 5 ∧ motzkinTriangleRowSum 3 = 13 ∧
          ∀ n : Nat, motzkinTriangleRowSum n = motzkinTrianglePrefix n n) := by
  constructor
  · exact motzkinTriangle_zero_zero
  · constructor
    · intro n
      exact motzkinTriangle_zero_step n
    · constructor
      · intro n k
        exact motzkinTriangle_recurrence n k
      · constructor
        · intro n
          exact motzkinTriangle_zero_eq_motzkinNumber n
        · constructor
          · intro n
            exact motzkinTriangleRowSum_prefix n
          · exact motzkinPrefixRowSum_export

end BEDC.Derived.MotzkinTriangleUp
