import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMapUp : Type where
  | mk (S R D F T Q A H C P N : BHist) : RegularCauchyMapUp
  deriving DecidableEq

def regularCauchyMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMapEncodeBHist h

def regularCauchyMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMapDecodeBHist tail)

private theorem RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMapToEventFlow : RegularCauchyMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMapUp.mk S R D F T Q A H C P N =>
      [[BMark.b0],
        regularCauchyMapEncodeBHist S,
        [BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyMapEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMapEncodeBHist N]

private def regularCauchyMapEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMapEventAtDefault index rest

def regularCauchyMapFromEventFlow (ef : EventFlow) : Option RegularCauchyMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMapUp.mk
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 1 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 3 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 5 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 7 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 9 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 11 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 13 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 15 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 17 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 19 ef))
      (regularCauchyMapDecodeBHist (regularCauchyMapEventAtDefault 21 ef)))

private theorem RegularCauchyMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyMapUp,
      regularCauchyMapFromEventFlow (regularCauchyMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D F T Q A H C P N =>
      change
        some
          (RegularCauchyMapUp.mk
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist S))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist R))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist D))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist F))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist T))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist Q))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist A))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist H))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist C))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist P))
            (regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist N))) =
          some (RegularCauchyMapUp.mk S R D F T Q A H C P N)
      rw [RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode F,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyMapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyMapUp} :
    regularCauchyMapToEventFlow x = regularCauchyMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMapFromEventFlow (regularCauchyMapToEventFlow x) =
        regularCauchyMapFromEventFlow (regularCauchyMapToEventFlow y) :=
    congrArg regularCauchyMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyMapTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMapBHistCarrier : BHistCarrier RegularCauchyMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMapToEventFlow
  fromEventFlow := regularCauchyMapFromEventFlow

instance regularCauchyMapChapterTasteGate : ChapterTasteGate RegularCauchyMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMapFromEventFlow (regularCauchyMapToEventFlow x) = some x
    exact RegularCauchyMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyMapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMapChapterTasteGate

theorem RegularCauchyMapTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyMapDecodeBHist (regularCauchyMapEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMapUp,
        regularCauchyMapFromEventFlow (regularCauchyMapToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyMapUp,
          regularCauchyMapToEventFlow x = regularCauchyMapToEventFlow y → x = y) ∧
          regularCauchyMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyMapTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyMapTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularCauchyMapTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyMapUp
