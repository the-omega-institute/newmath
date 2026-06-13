import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrobeniusCoinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrobeniusCoinUp : Type where
  | mk (A B G C W H T P N : BHist) : FrobeniusCoinUp

def frobeniusCoinEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frobeniusCoinEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frobeniusCoinEncodeBHist h

def frobeniusCoinDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frobeniusCoinDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frobeniusCoinDecodeBHist tail)

private theorem FrobeniusCoinTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, frobeniusCoinDecodeBHist (frobeniusCoinEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem FrobeniusCoinTasteGate_single_carrier_alignment_some_mk_congr
    {A' B' G' C' W' H' T' P' N' A B G C W H T P N : BHist}
    (hA : A' = A) (hB : B' = B) (hG : G' = G) (hC : C' = C)
    (hW : W' = W) (hH : H' = H) (hT : T' = T) (hP : P' = P) (hN : N' = N) :
    some (FrobeniusCoinUp.mk A' B' G' C' W' H' T' P' N') =
      some (FrobeniusCoinUp.mk A B G C W H T P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hG
  cases hC
  cases hW
  cases hH
  cases hT
  cases hP
  cases hN
  rfl

def frobeniusCoinFields : FrobeniusCoinUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrobeniusCoinUp.mk A B G C W H T P N => [A, B, G, C, W, H, T, P, N]

def frobeniusCoinToEventFlow : FrobeniusCoinUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (frobeniusCoinFields x).map frobeniusCoinEncodeBHist

private def frobeniusCoinEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frobeniusCoinEventAtDefault index rest

def frobeniusCoinFromEventFlow (ef : EventFlow) : Option FrobeniusCoinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FrobeniusCoinUp.mk
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 0 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 1 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 2 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 3 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 4 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 5 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 6 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 7 ef))
      (frobeniusCoinDecodeBHist (frobeniusCoinEventAtDefault 8 ef)))

private theorem FrobeniusCoinTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FrobeniusCoinUp, frobeniusCoinFromEventFlow (frobeniusCoinToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B G C W H T P N =>
      exact
        FrobeniusCoinTasteGate_single_carrier_alignment_some_mk_congr
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode A)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode B)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode G)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode C)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode W)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode H)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode T)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode P)
          (FrobeniusCoinTasteGate_single_carrier_alignment_decode N)

private theorem FrobeniusCoinTasteGate_single_carrier_alignment_injective
    {x y : FrobeniusCoinUp} :
    frobeniusCoinToEventFlow x = frobeniusCoinToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frobeniusCoinFromEventFlow (frobeniusCoinToEventFlow x) =
        frobeniusCoinFromEventFlow (frobeniusCoinToEventFlow y) :=
    congrArg frobeniusCoinFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FrobeniusCoinTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrobeniusCoinTasteGate_single_carrier_alignment_round_trip y)))

instance frobeniusCoinBHistCarrier : BHistCarrier FrobeniusCoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frobeniusCoinToEventFlow
  fromEventFlow := frobeniusCoinFromEventFlow

instance frobeniusCoinChapterTasteGate : ChapterTasteGate FrobeniusCoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frobeniusCoinFromEventFlow (frobeniusCoinToEventFlow x) = some x
    exact FrobeniusCoinTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrobeniusCoinTasteGate_single_carrier_alignment_injective heq)

theorem FrobeniusCoinTasteGate_single_carrier_alignment :
    (∀ h : BHist, frobeniusCoinDecodeBHist (frobeniusCoinEncodeBHist h) = h) ∧
      (∀ x : FrobeniusCoinUp, frobeniusCoinFromEventFlow (frobeniusCoinToEventFlow x) = some x) ∧
      (∀ x y : FrobeniusCoinUp,
        frobeniusCoinToEventFlow x = frobeniusCoinToEventFlow y → x = y) ∧
      frobeniusCoinEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact FrobeniusCoinTasteGate_single_carrier_alignment_decode
  · constructor
    · exact FrobeniusCoinTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FrobeniusCoinTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.FrobeniusCoinUp
