import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySheafUp : Type where
  | mk (U R O Q E H C P N : BHist) : RegularCauchySheafUp
  deriving DecidableEq

def regularCauchySheafEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySheafEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySheafEncodeBHist h

def regularCauchySheafDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySheafDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySheafDecodeBHist tail)

private theorem RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySheafToEventFlow : RegularCauchySheafUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySheafUp.mk U R O Q E H C P N =>
      [[BMark.b0],
        regularCauchySheafEncodeBHist U,
        [BMark.b1, BMark.b0],
        regularCauchySheafEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchySheafEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySheafEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySheafEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySheafEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySheafEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchySheafEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchySheafEncodeBHist N]

private def regularCauchySheafEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySheafEventAtDefault index rest

def regularCauchySheafFromEventFlow (ef : EventFlow) : Option RegularCauchySheafUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySheafUp.mk
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 1 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 3 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 5 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 7 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 9 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 11 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 13 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 15 ef))
      (regularCauchySheafDecodeBHist (regularCauchySheafEventAtDefault 17 ef)))

private theorem RegularCauchySheafTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySheafUp,
      regularCauchySheafFromEventFlow (regularCauchySheafToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U R O Q E H C P N =>
      change
        some
          (RegularCauchySheafUp.mk
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist U))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist R))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist O))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist Q))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist E))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist H))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist C))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist P))
            (regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist N))) =
          some (RegularCauchySheafUp.mk U R O Q E H C P N)
      rw [RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode U,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode O,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchySheafTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySheafUp} :
    regularCauchySheafToEventFlow x = regularCauchySheafToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySheafFromEventFlow (regularCauchySheafToEventFlow x) =
        regularCauchySheafFromEventFlow (regularCauchySheafToEventFlow y) :=
    congrArg regularCauchySheafFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchySheafTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchySheafTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySheafBHistCarrier : BHistCarrier RegularCauchySheafUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySheafToEventFlow
  fromEventFlow := regularCauchySheafFromEventFlow

instance regularCauchySheafChapterTasteGate : ChapterTasteGate RegularCauchySheafUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySheafFromEventFlow (regularCauchySheafToEventFlow x) = some x
    exact RegularCauchySheafTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchySheafTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySheafUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySheafChapterTasteGate

theorem RegularCauchySheafTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchySheafDecodeBHist (regularCauchySheafEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySheafUp,
        regularCauchySheafFromEventFlow (regularCauchySheafToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySheafUp,
          regularCauchySheafToEventFlow x = regularCauchySheafToEventFlow y → x = y) ∧
          regularCauchySheafEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchySheafTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchySheafTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchySheafTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchySheafUp
