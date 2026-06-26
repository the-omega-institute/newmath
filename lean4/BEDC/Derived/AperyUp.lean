import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.CatalanUp

namespace BEDC.Derived.AperyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_length natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev UnaryOne : BHist :=
  BHist.e1 BHist.Empty

-- 有限求和窗口使用 `List.range (n + 1)`，即索引 `0, ..., n`。
def aperyIndexList (n : Nat) : List Nat :=
  List.range (n + 1)

def natListSum (xs : List Nat) (f : Nat -> Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + natListSum rest f

def natSquare (n : Nat) : Nat :=
  n * n

def natCube (n : Nat) : Nat :=
  n * n * n

-- ζ(3) 逼近所用的 Apéry 分子型整数项。
def aperyATerm (n k : Nat) : Nat :=
  natSquare (C n k) * natSquare (C (n + k) k)

def aperyA (n : Nat) : Nat :=
  natListSum (aperyIndexList n) (aperyATerm n)

-- ζ(2) 逼近所用的 Apéry 型整数项。
def aperyBTerm (n k : Nat) : Nat :=
  natSquare (C n k) * C (n + k) k

def aperyB (n : Nat) : Nat :=
  natListSum (aperyIndexList n) (aperyBTerm n)

def aperyPair (n : Nat) : Nat × Nat :=
  (aperyA n, aperyB n)

def aperyAFn (n : BHist) : BHist :=
  natToUnary (aperyA (bwordLength n))

def aperyBFn (n : BHist) : BHist :=
  natToUnary (aperyB (bwordLength n))

def aperyPairFn (n : BHist) : BHist × BHist :=
  (aperyAFn n, aperyBFn n)

def aperyARecurrenceCoeff (n : Nat) : Nat :=
  34 * natCube n - 51 * natSquare n + 27 * n - 5

def aperyARecurrenceAt (n : Nat) : Prop :=
  natCube n * aperyA n =
    aperyARecurrenceCoeff n * aperyA (n - 1) -
      natCube (n - 1) * aperyA (n - 2)

theorem aperyA_sum_definition (n : Nat) :
    aperyA n = natListSum (aperyIndexList n) (aperyATerm n) := by
  rfl

theorem aperyB_sum_definition (n : Nat) :
    aperyB n = natListSum (aperyIndexList n) (aperyBTerm n) := by
  rfl

theorem aperyAFn_unary_result (n : BHist) :
    UnaryHistory (aperyAFn n) := by
  unfold aperyAFn
  exact natToUnary_unary _

theorem aperyBFn_unary_result (n : BHist) :
    UnaryHistory (aperyBFn n) := by
  unfold aperyBFn
  exact natToUnary_unary _

theorem aperyAFn_natToUnary (n : Nat) :
    aperyAFn (natToUnary n) = natToUnary (aperyA n) := by
  unfold aperyAFn
  rw [natToUnary_length]

theorem aperyBFn_natToUnary (n : Nat) :
    aperyBFn (natToUnary n) = natToUnary (aperyB n) := by
  unfold aperyBFn
  rw [natToUnary_length]

theorem aperyA_zero :
    aperyA 0 = 1 := by
  rfl

theorem aperyA_one :
    aperyA 1 = 5 := by
  rfl

theorem aperyA_two :
    aperyA 2 = 73 := by
  rfl

theorem aperyA_three :
    aperyA 3 = 1445 := by
  rfl

theorem aperyA_four :
    aperyA 4 = 33001 := by
  rfl

theorem aperyB_zero :
    aperyB 0 = 1 := by
  rfl

theorem aperyB_one :
    aperyB 1 = 3 := by
  rfl

theorem aperyB_two :
    aperyB 2 = 19 := by
  rfl

theorem aperyB_three :
    aperyB 3 = 147 := by
  rfl

theorem aperyB_four :
    aperyB 4 = 1251 := by
  rfl

theorem aperyPair_zero :
    aperyPair 0 = (1, 1) := by
  rfl

theorem aperyPair_one :
    aperyPair 1 = (5, 3) := by
  rfl

theorem aperyPair_two :
    aperyPair 2 = (73, 19) := by
  rfl

theorem aperyPair_three :
    aperyPair 3 = (1445, 147) := by
  rfl

theorem aperyAFn_zero :
    aperyAFn BHist.Empty = UnaryOne := by
  rfl

theorem aperyBFn_zero :
    aperyBFn BHist.Empty = UnaryOne := by
  rfl

theorem aperyA_recurrence_at_two :
    aperyARecurrenceAt 2 := by
  rfl

theorem aperyA_recurrence_at_three :
    aperyARecurrenceAt 3 := by
  rfl

theorem aperyA_recurrence_at_four :
    aperyARecurrenceAt 4 := by
  rfl

theorem aperyA_recurrence_window :
    aperyARecurrenceAt 2 ∧ aperyARecurrenceAt 3 ∧ aperyARecurrenceAt 4 := by
  constructor
  · exact aperyA_recurrence_at_two
  · constructor
    · exact aperyA_recurrence_at_three
    · exact aperyA_recurrence_at_four

theorem AperyUp_constructive_export :
    aperyA 0 = 1 ∧
      aperyA 1 = 5 ∧
      aperyA 2 = 73 ∧
      aperyA 3 = 1445 ∧
      aperyA 4 = 33001 ∧
      aperyB 0 = 1 ∧
      aperyB 1 = 3 ∧
      aperyB 2 = 19 ∧
      aperyB 3 = 147 ∧
      aperyB 4 = 1251 ∧
      (∀ n : BHist, UnaryHistory (aperyAFn n)) ∧
      (∀ n : BHist, UnaryHistory (aperyBFn n)) ∧
      aperyARecurrenceAt 2 ∧
      aperyARecurrenceAt 3 ∧
      aperyARecurrenceAt 4 := by
  constructor
  · exact aperyA_zero
  · constructor
    · exact aperyA_one
    · constructor
      · exact aperyA_two
      · constructor
        · exact aperyA_three
        · constructor
          · exact aperyA_four
          · constructor
            · exact aperyB_zero
            · constructor
              · exact aperyB_one
              · constructor
                · exact aperyB_two
                · constructor
                  · exact aperyB_three
                  · constructor
                    · exact aperyB_four
                    · constructor
                      · intro n
                        exact aperyAFn_unary_result n
                      · constructor
                        · intro n
                          exact aperyBFn_unary_result n
                        · exact aperyA_recurrence_window

end BEDC.Derived.AperyUp
