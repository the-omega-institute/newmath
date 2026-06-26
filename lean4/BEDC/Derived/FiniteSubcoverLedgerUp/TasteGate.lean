import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSubcoverLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSubcoverLedgerUp : Type where
  | mk (K T B D S U H C P N : BHist) : FiniteSubcoverLedgerUp
  deriving DecidableEq

def finiteSubcoverLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSubcoverLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSubcoverLedgerEncodeBHist h

def finiteSubcoverLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSubcoverLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSubcoverLedgerDecodeBHist tail)

private theorem FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FiniteSubcoverLedgerTasteGate_single_carrier_alignment_fields :
    FiniteSubcoverLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSubcoverLedgerUp.mk K T B D S U H C P N => [K, T, B, D, S, U, H, C, P, N]

def finiteSubcoverLedgerToEventFlow : FiniteSubcoverLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (FiniteSubcoverLedgerTasteGate_single_carrier_alignment_fields x).map
        finiteSubcoverLedgerEncodeBHist

private def finiteSubcoverLedgerEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSubcoverLedgerEventAt index rest

def finiteSubcoverLedgerFromEventFlow (ef : EventFlow) :
    Option FiniteSubcoverLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSubcoverLedgerUp.mk
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 0 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 1 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 2 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 3 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 4 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 5 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 6 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 7 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 8 ef))
      (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEventAt 9 ef)))

private theorem FiniteSubcoverLedgerTasteGate_single_carrier_alignment_round_trip
    (x : FiniteSubcoverLedgerUp) :
    finiteSubcoverLedgerFromEventFlow (finiteSubcoverLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K T B D S U H C P N =>
      change
        some
          (FiniteSubcoverLedgerUp.mk
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist K))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist T))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist B))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist D))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist S))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist U))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist H))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist C))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist P))
            (finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist N))) =
          some (FiniteSubcoverLedgerUp.mk K T B D S U H C P N)
      rw [FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode K,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode T,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode B,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode D,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode S,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode U,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode H,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode C,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode P,
        FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteSubcoverLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteSubcoverLedgerUp} :
    finiteSubcoverLedgerToEventFlow x = finiteSubcoverLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSubcoverLedgerFromEventFlow (finiteSubcoverLedgerToEventFlow x) =
        finiteSubcoverLedgerFromEventFlow (finiteSubcoverLedgerToEventFlow y) :=
    congrArg finiteSubcoverLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSubcoverLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteSubcoverLedgerTasteGate_single_carrier_alignment_round_trip y)))

instance finiteSubcoverLedgerBHistCarrier : BHistCarrier FiniteSubcoverLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSubcoverLedgerToEventFlow
  fromEventFlow := finiteSubcoverLedgerFromEventFlow

instance finiteSubcoverLedgerChapterTasteGate :
    ChapterTasteGate FiniteSubcoverLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSubcoverLedgerFromEventFlow (finiteSubcoverLedgerToEventFlow x) = some x
    exact FiniteSubcoverLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteSubcoverLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteSubcoverLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteSubcoverLedgerDecodeBHist (finiteSubcoverLedgerEncodeBHist h) = h) ∧
      FiniteSubcoverLedgerTasteGate_single_carrier_alignment_fields
          (FiniteSubcoverLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact FiniteSubcoverLedgerTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.FiniteSubcoverLedgerUp
