import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalSealUp : Type where
  | mk (F S E R L G H C P N : BHist) : RegularCauchyDiagonalSealUp
  deriving DecidableEq

def regularCauchyDiagonalSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalSealEncodeBHist h

def regularCauchyDiagonalSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalSealDecodeBHist tail)

private theorem RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDiagonalSealFields :
    RegularCauchyDiagonalSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalSealUp.mk F S E R L G H C P N => [F, S, E, R, L, G, H, C, P, N]

def regularCauchyDiagonalSealToEventFlow :
    RegularCauchyDiagonalSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyDiagonalSealFields x).map regularCauchyDiagonalSealEncodeBHist

private def regularCauchyDiagonalSealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDiagonalSealEventAt index rest

def regularCauchyDiagonalSealFromEventFlow :
    EventFlow → Option RegularCauchyDiagonalSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyDiagonalSealUp.mk
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 0 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 1 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 2 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 3 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 4 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 5 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 6 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 7 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 8 ef))
        (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEventAt 9 ef)))

private theorem RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyDiagonalSealUp) :
    regularCauchyDiagonalSealFromEventFlow
        (regularCauchyDiagonalSealToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F S E R L G H C P N =>
      change
        some
          (RegularCauchyDiagonalSealUp.mk
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist F))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist S))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist E))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist R))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist L))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist G))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist H))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist C))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist P))
            (regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist N))) =
          some (RegularCauchyDiagonalSealUp.mk F S E R L G H C P N)
      rw [RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode F,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode G,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyDiagonalSealUp} :
    regularCauchyDiagonalSealToEventFlow x =
        regularCauchyDiagonalSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDiagonalSealFromEventFlow
          (regularCauchyDiagonalSealToEventFlow x) =
        regularCauchyDiagonalSealFromEventFlow
          (regularCauchyDiagonalSealToEventFlow y) :=
    congrArg regularCauchyDiagonalSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyDiagonalSealBHistCarrier :
    BHistCarrier RegularCauchyDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalSealToEventFlow
  fromEventFlow := regularCauchyDiagonalSealFromEventFlow

instance regularCauchyDiagonalSealChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalSealFromEventFlow
          (regularCauchyDiagonalSealToEventFlow x) =
        some x
    exact RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyDiagonalSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDiagonalSealChapterTasteGate

theorem RegularCauchyDiagonalSealTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyDiagonalSealDecodeBHist (regularCauchyDiagonalSealEncodeBHist h) = h) ∧
      (forall x : RegularCauchyDiagonalSealUp,
        regularCauchyDiagonalSealFromEventFlow (regularCauchyDiagonalSealToEventFlow x) =
          some x) ∧
        (forall x y : RegularCauchyDiagonalSealUp,
          regularCauchyDiagonalSealToEventFlow x = regularCauchyDiagonalSealToEventFlow y ->
            x = y) ∧
          regularCauchyDiagonalSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact RegularCauchyDiagonalSealTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.RegularCauchyDiagonalSealUp
