import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRealUp : Type where
  | mk (S D Q K E H C P N : BHist) : RegularCauchyRealUp
  deriving DecidableEq

def regularCauchyRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRealEncodeBHist h

def regularCauchyRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRealDecodeBHist tail)

private theorem RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchyRealTasteGate_single_carrier_alignment_fields :
    RegularCauchyRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRealUp.mk S D Q K E H C P N => [S, D, Q, K, E, H, C, P, N]

def regularCauchyRealToEventFlow : RegularCauchyRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (RegularCauchyRealTasteGate_single_carrier_alignment_fields x).map
      regularCauchyRealEncodeBHist

private def regularCauchyRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyRealEventAt index rest

def regularCauchyRealFromEventFlow (ef : EventFlow) : Option RegularCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyRealUp.mk
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 0 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 1 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 2 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 3 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 4 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 5 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 6 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 7 ef))
      (regularCauchyRealDecodeBHist (regularCauchyRealEventAt 8 ef)))

private theorem RegularCauchyRealTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyRealUp) :
    regularCauchyRealFromEventFlow (regularCauchyRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D Q K E H C P N =>
      change
        some
          (RegularCauchyRealUp.mk
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist S))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist D))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist Q))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist K))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist E))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist H))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist C))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist P))
            (regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist N))) =
          some (RegularCauchyRealUp.mk S D Q K E H C P N)
      rw [RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode K,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyRealUp} :
    regularCauchyRealToEventFlow x = regularCauchyRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyRealFromEventFlow (regularCauchyRealToEventFlow x) =
        regularCauchyRealFromEventFlow (regularCauchyRealToEventFlow y) :=
    congrArg regularCauchyRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyRealTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyRealBHistCarrier : BHistCarrier RegularCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRealToEventFlow
  fromEventFlow := regularCauchyRealFromEventFlow

instance regularCauchyRealChapterTasteGate : ChapterTasteGate RegularCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyRealFromEventFlow (regularCauchyRealToEventFlow x) = some x
    exact RegularCauchyRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyRealDecodeBHist (regularCauchyRealEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyRealUp,
        regularCauchyRealFromEventFlow (regularCauchyRealToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyRealUp,
          regularCauchyRealToEventFlow x = regularCauchyRealToEventFlow y → x = y) ∧
          regularCauchyRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyRealTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyRealUp
