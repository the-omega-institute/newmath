import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.MotzkinUp

namespace BEDC.Derived.RiordanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

/-!
  Riordan 数以乘法形式的三项递推闭生成。构造子 `step`
  对应 `(n+3) R(n+2) = (n+1) (2 R(n+1) + 3 R(n))`。
-/

def riordanRecurrenceEq (n previous current next : Nat) : Prop :=
  (n + 3) * next = (n + 1) * (2 * current + 3 * previous)

inductive RiordanNat : Nat -> Nat -> Prop where
  | zero : RiordanNat 0 1
  | one : RiordanNat 1 0
  | step {n previous current next : Nat} :
      RiordanNat n previous -> RiordanNat (n + 1) current ->
        riordanRecurrenceEq n previous current next ->
          RiordanNat (n + 2) next

def Riordan (n value : BHist) : Prop :=
  ∃ index : Nat, ∃ count : Nat,
    n = natToUnary index ∧ value = natToUnary count ∧ RiordanNat index count

theorem riordanNatToUnaryAppend (m n : Nat) :
    append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

theorem riordanNatToUnaryAddRel (m n : Nat) :
    NatAdd (natToUnary m) (natToUnary n) (natToUnary (m + n)) := by
  exact
    ⟨natToUnary_unary m, natToUnary_unary n,
      cont_intro (riordanNatToUnaryAppend m n).symm⟩

theorem riordan_of_nat {index count : Nat} :
    RiordanNat index count -> Riordan (natToUnary index) (natToUnary count) := by
  intro witness
  exact ⟨index, count, rfl, rfl, witness⟩

theorem riordanNat_zero : RiordanNat 0 1 :=
  RiordanNat.zero

theorem riordanNat_one : RiordanNat 1 0 :=
  RiordanNat.one

theorem riordanRecurrence {n previous current next : Nat} :
    RiordanNat n previous -> RiordanNat (n + 1) current ->
      riordanRecurrenceEq n previous current next ->
        RiordanNat (n + 2) next := by
  intro previousWitness currentWitness recurrence
  exact RiordanNat.step previousWitness currentWitness recurrence

theorem riordanNat_two : RiordanNat 2 1 :=
  riordanRecurrence riordanNat_zero riordanNat_one rfl

theorem riordanNat_three : RiordanNat 3 1 :=
  riordanRecurrence riordanNat_one riordanNat_two rfl

theorem riordanNat_four : RiordanNat 4 3 :=
  riordanRecurrence riordanNat_two riordanNat_three rfl

theorem riordanNat_five : RiordanNat 5 6 :=
  riordanRecurrence riordanNat_three riordanNat_four rfl

theorem riordanNat_six : RiordanNat 6 15 :=
  riordanRecurrence riordanNat_four riordanNat_five rfl

theorem riordanNat_seven : RiordanNat 7 36 :=
  riordanRecurrence riordanNat_five riordanNat_six rfl

theorem riordanNat_eight : RiordanNat 8 91 :=
  riordanRecurrence riordanNat_six riordanNat_seven rfl

theorem riordanNoSizeOne : RiordanNat 1 0 :=
  riordanNat_one

theorem riordanSmallValues :
    RiordanNat 0 1 ∧ RiordanNat 1 0 ∧ RiordanNat 2 1 ∧
      RiordanNat 3 1 ∧ RiordanNat 4 3 ∧ RiordanNat 5 6 ∧
        RiordanNat 6 15 ∧ RiordanNat 7 36 ∧ RiordanNat 8 91 := by
  constructor
  · exact riordanNat_zero
  · constructor
    · exact riordanNat_one
    · constructor
      · exact riordanNat_two
      · constructor
        · exact riordanNat_three
        · constructor
          · exact riordanNat_four
          · constructor
            · exact riordanNat_five
            · constructor
              · exact riordanNat_six
              · constructor
                · exact riordanNat_seven
                · exact riordanNat_eight

theorem riordan_zero : Riordan (natToUnary 0) (natToUnary 1) :=
  riordan_of_nat riordanNat_zero

theorem riordan_one : Riordan (natToUnary 1) (natToUnary 0) :=
  riordan_of_nat riordanNat_one

theorem riordan_two : Riordan (natToUnary 2) (natToUnary 1) :=
  riordan_of_nat riordanNat_two

theorem riordan_three : Riordan (natToUnary 3) (natToUnary 1) :=
  riordan_of_nat riordanNat_three

theorem riordan_four : Riordan (natToUnary 4) (natToUnary 3) :=
  riordan_of_nat riordanNat_four

theorem riordan_five : Riordan (natToUnary 5) (natToUnary 6) :=
  riordan_of_nat riordanNat_five

theorem riordan_six : Riordan (natToUnary 6) (natToUnary 15) :=
  riordan_of_nat riordanNat_six

theorem riordan_seven : Riordan (natToUnary 7) (natToUnary 36) :=
  riordan_of_nat riordanNat_seven

theorem riordan_eight : Riordan (natToUnary 8) (natToUnary 91) :=
  riordan_of_nat riordanNat_eight

def RiordanMotzkinSplit (n motzkin current next : Nat) : Prop :=
  BEDC.Derived.MotzkinUp.Motzkin (natToUnary n) (natToUnary motzkin) ∧
    Riordan (natToUnary n) (natToUnary current) ∧
      Riordan (natToUnary (n + 1)) (natToUnary next) ∧
        NatAdd (natToUnary current) (natToUnary next) (natToUnary motzkin)

theorem riordanMotzkinSplit_zero : RiordanMotzkinSplit 0 1 1 0 := by
  unfold RiordanMotzkinSplit
  constructor
  · exact BEDC.Derived.MotzkinUp.motzkin_zero
  · constructor
    · exact riordan_zero
    · constructor
      · exact riordan_one
      · exact riordanNatToUnaryAddRel 1 0

theorem riordanMotzkinSplit_one : RiordanMotzkinSplit 1 1 0 1 := by
  unfold RiordanMotzkinSplit
  constructor
  · exact BEDC.Derived.MotzkinUp.motzkin_one
  · constructor
    · exact riordan_one
    · constructor
      · exact riordan_two
      · exact riordanNatToUnaryAddRel 0 1

theorem riordanMotzkinSplit_two : RiordanMotzkinSplit 2 2 1 1 := by
  unfold RiordanMotzkinSplit
  constructor
  · exact BEDC.Derived.MotzkinUp.motzkin_two
  · constructor
    · exact riordan_two
    · constructor
      · exact riordan_three
      · exact riordanNatToUnaryAddRel 1 1

theorem riordanMotzkinSplit_three : RiordanMotzkinSplit 3 4 1 3 := by
  unfold RiordanMotzkinSplit
  constructor
  · exact BEDC.Derived.MotzkinUp.motzkin_three
  · constructor
    · exact riordan_three
    · constructor
      · exact riordan_four
      · exact riordanNatToUnaryAddRel 1 3

theorem riordanMotzkinSplit_four : RiordanMotzkinSplit 4 9 3 6 := by
  unfold RiordanMotzkinSplit
  constructor
  · exact BEDC.Derived.MotzkinUp.motzkin_four
  · constructor
    · exact riordan_four
    · constructor
      · exact riordan_five
      · exact riordanNatToUnaryAddRel 3 6

theorem riordanMotzkinSplit_five : RiordanMotzkinSplit 5 21 6 15 := by
  unfold RiordanMotzkinSplit
  constructor
  · exact BEDC.Derived.MotzkinUp.motzkin_five
  · constructor
    · exact riordan_five
    · constructor
      · exact riordan_six
      · exact riordanNatToUnaryAddRel 6 15

theorem riordanMotzkinSmallSplits :
    RiordanMotzkinSplit 0 1 1 0 ∧ RiordanMotzkinSplit 1 1 0 1 ∧
      RiordanMotzkinSplit 2 2 1 1 ∧ RiordanMotzkinSplit 3 4 1 3 ∧
        RiordanMotzkinSplit 4 9 3 6 ∧ RiordanMotzkinSplit 5 21 6 15 := by
  constructor
  · exact riordanMotzkinSplit_zero
  · constructor
    · exact riordanMotzkinSplit_one
    · constructor
      · exact riordanMotzkinSplit_two
      · constructor
        · exact riordanMotzkinSplit_three
        · constructor
          · exact riordanMotzkinSplit_four
          · exact riordanMotzkinSplit_five

theorem riordanCatalanBoundaryRelation :
    (Riordan (natToUnary 0) (natToUnary 1) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 0) (natToUnary 1)) ∧
    (Riordan (natToUnary 2) (natToUnary 1) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 1) (natToUnary 1)) := by
  constructor
  · constructor
    · exact riordan_zero
    · exact BEDC.Derived.CatalanUp.catalan_zero
  · constructor
    · exact riordan_two
    · exact BEDC.Derived.CatalanUp.catalan_one

theorem riordanBinomialAnchor :
    BEDC.Derived.BinomialIdentitiesUp.C 0 0 = 1 ∧ RiordanNat 0 1 := by
  constructor
  · exact BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right 0
  · exact riordanNat_zero

theorem RiordanUp_constructive_export :
    RiordanNat 0 1 ∧ RiordanNat 1 0 ∧ RiordanNat 2 1 ∧
      RiordanNat 3 1 ∧ RiordanNat 4 3 ∧ RiordanNat 5 6 ∧
        RiordanNat 6 15 ∧ RiordanNat 7 36 ∧
          (∀ {n previous current next : Nat},
            RiordanNat n previous -> RiordanNat (n + 1) current ->
              riordanRecurrenceEq n previous current next ->
                RiordanNat (n + 2) next) ∧
          RiordanMotzkinSplit 0 1 1 0 ∧
          RiordanMotzkinSplit 1 1 0 1 ∧
          RiordanMotzkinSplit 2 2 1 1 ∧
          (Riordan (natToUnary 0) (natToUnary 1) ∧
            BEDC.Derived.CatalanUp.Catalan (natToUnary 0) (natToUnary 1)) := by
  constructor
  · exact riordanNat_zero
  · constructor
    · exact riordanNat_one
    · constructor
      · exact riordanNat_two
      · constructor
        · exact riordanNat_three
        · constructor
          · exact riordanNat_four
          · constructor
            · exact riordanNat_five
            · constructor
              · exact riordanNat_six
              · constructor
                · exact riordanNat_seven
                · constructor
                  · intro n previous current next previousWitness currentWitness recurrence
                    exact riordanRecurrence previousWitness currentWitness recurrence
                  · constructor
                    · exact riordanMotzkinSplit_zero
                    · constructor
                      · exact riordanMotzkinSplit_one
                      · constructor
                        · exact riordanMotzkinSplit_two
                        · constructor
                          · exact riordan_zero
                          · exact BEDC.Derived.CatalanUp.catalan_zero

end BEDC.Derived.RiordanUp
