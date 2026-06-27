import BEDC.Derived.PadicValuationUp
import BEDC.Derived.PreorderUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PrimeAdicParityEnergyWindow

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.PadicValuationUp
open BEDC.Derived.PreorderUp
open BEDC.Derived.PrimeUp

inductive Parity where
  | even
  | odd

def parityFlip : Parity -> Parity
  | Parity.even => Parity.odd
  | Parity.odd => Parity.even

def parityOfUnary : BHist -> Parity
  | BHist.Empty => Parity.even
  | BHist.e0 _ => Parity.even
  | BHist.e1 tail => parityFlip (parityOfUnary tail)

def parityEnergyUnit : BHist :=
  BHist.e1 BHist.Empty

def parityDefectEnergy (expected observed : Parity) : BHist :=
  match expected, observed with
  | Parity.even, Parity.even => BHist.Empty
  | Parity.even, Parity.odd => parityEnergyUnit
  | Parity.odd, Parity.even => parityEnergyUnit
  | Parity.odd, Parity.odd => BHist.Empty

structure PrimeAdicParityRow where
  prime : BHist
  parityIndex : BHist
  sample : BHist
  valuation : BHist
  prime_cert : NatPrime prime
  index_unary : UnaryHistory parityIndex
  valuation_cert : padicValuationNat prime sample valuation

def rowParityEnergy (row : PrimeAdicParityRow) : BHist :=
  parityDefectEnergy (parityOfUnary row.parityIndex) (parityOfUnary row.valuation)

def windowEnergy : List PrimeAdicParityRow -> BHist
  | [] => BHist.Empty
  | row :: rows => append (rowParityEnergy row) (windowEnergy rows)

def windowLengthEnergyBound : List PrimeAdicParityRow -> BHist
  | [] => BHist.Empty
  | _row :: rows => append parityEnergyUnit (windowLengthEnergyBound rows)

def evenParityRows : List PrimeAdicParityRow -> List PrimeAdicParityRow
  | [] => []
  | row :: rows =>
      match parityOfUnary row.parityIndex with
      | Parity.even => row :: evenParityRows rows
      | Parity.odd => evenParityRows rows

def oddParityRows : List PrimeAdicParityRow -> List PrimeAdicParityRow
  | [] => []
  | row :: rows =>
      match parityOfUnary row.parityIndex with
      | Parity.even => oddParityRows rows
      | Parity.odd => row :: oddParityRows rows

theorem parityFlip_involutive (p : Parity) :
    parityFlip (parityFlip p) = p := by
  cases p
  · rfl
  · rfl

theorem parityDefectEnergy_unary (expected observed : Parity) :
    UnaryHistory (parityDefectEnergy expected observed) := by
  cases expected <;> cases observed <;> exact unary_e1_closed unary_empty

theorem parityDefectEnergy_le_unit (expected observed : Parity) :
    PreorderPrefixLE (parityDefectEnergy expected observed) parityEnergyUnit := by
  cases expected <;> cases observed
  · exact PreorderPrefixLE_empty_left_iff_unary.mpr (unary_e1_closed unary_empty)
  · exact PreorderPrefixLE_of_hsame (hsame_refl parityEnergyUnit)
  · exact PreorderPrefixLE_of_hsame (hsame_refl parityEnergyUnit)
  · exact PreorderPrefixLE_empty_left_iff_unary.mpr (unary_e1_closed unary_empty)

theorem rowParityEnergy_unary (row : PrimeAdicParityRow) :
    UnaryHistory (rowParityEnergy row) := by
  unfold rowParityEnergy
  exact parityDefectEnergy_unary _ _

theorem rowParityEnergy_le_unit (row : PrimeAdicParityRow) :
    PreorderPrefixLE (rowParityEnergy row) parityEnergyUnit := by
  unfold rowParityEnergy
  exact parityDefectEnergy_le_unit _ _

theorem windowEnergy_unary (rows : List PrimeAdicParityRow) :
    UnaryHistory (windowEnergy rows) := by
  induction rows with
  | nil =>
      exact unary_empty
  | cons row rows ih =>
      exact unary_append_closed (rowParityEnergy_unary row) ih

theorem windowLengthEnergyBound_unary (rows : List PrimeAdicParityRow) :
    UnaryHistory (windowLengthEnergyBound rows) := by
  induction rows with
  | nil =>
      exact unary_empty
  | cons _row rows ih =>
      exact unary_append_closed (unary_e1_closed unary_empty) ih

theorem windowEnergy_bounded (rows : List PrimeAdicParityRow) :
    PreorderPrefixLE (windowEnergy rows) (windowLengthEnergyBound rows) := by
  induction rows with
  | nil =>
      exact PreorderPrefixLE_of_hsame (hsame_refl BHist.Empty)
  | cons row rows ih =>
      have headStep :
          PreorderPrefixLE
            (append (rowParityEnergy row) (windowEnergy rows))
            (append parityEnergyUnit (windowEnergy rows)) :=
        PreorderPrefixLE_append_right_context
          (windowEnergy_unary rows) (rowParityEnergy_le_unit row)
      have tailStep :
          PreorderPrefixLE
            (append parityEnergyUnit (windowEnergy rows))
            (append parityEnergyUnit (windowLengthEnergyBound rows)) :=
        PreorderPrefixLE_append_left_context ih
      exact PreorderPrefixLE_trans headStep tailStep

theorem windowEnergy_cons_decomposition (row : PrimeAdicParityRow)
    (rows : List PrimeAdicParityRow) :
    hsame (windowEnergy (row :: rows))
      (append (rowParityEnergy row) (windowEnergy rows)) := by
  rfl

theorem rowParity_decomposition (row : PrimeAdicParityRow) :
    parityOfUnary row.parityIndex = Parity.even ∨
      parityOfUnary row.parityIndex = Parity.odd := by
  cases parityOfUnary row.parityIndex
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem evenOddWindow_decomposition (rows : List PrimeAdicParityRow) :
    List.Nodup rows ->
      ∀ row : PrimeAdicParityRow,
        row ∈ rows ->
          parityOfUnary row.parityIndex = Parity.even ∨
            parityOfUnary row.parityIndex = Parity.odd := by
  intro _nodup row _member
  exact rowParity_decomposition row

theorem rowValuation_unique {row : PrimeAdicParityRow} {other : BHist} :
    padicValuationNat row.prime row.sample other ->
      hsame row.valuation other := by
  intro otherValuation
  exact padicValuationNat_unique row.valuation_cert otherValuation

def valuationParityEnergyWindowTarget :
    List PrimeAdicParityRow -> BHist -> Prop :=
  fun rows bound =>
    hsame bound (windowLengthEnergyBound rows) ∧
      PreorderPrefixLE (windowEnergy rows) bound

theorem windowEnergy_has_length_bound (rows : List PrimeAdicParityRow) :
    valuationParityEnergyWindowTarget rows (windowLengthEnergyBound rows) := by
  exact ⟨hsame_refl (windowLengthEnergyBound rows), windowEnergy_bounded rows⟩

end BEDC.Derived.PrimeAdicParityEnergyWindow
