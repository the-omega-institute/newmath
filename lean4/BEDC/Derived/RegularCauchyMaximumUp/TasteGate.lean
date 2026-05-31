import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMaximumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMaximumUp : Type where
  | mk (X Y WX WY D S A U R E H C P N : BHist) : RegularCauchyMaximumUp
  deriving DecidableEq

def regularCauchyMaximumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMaximumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMaximumEncodeBHist h

def regularCauchyMaximumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMaximumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMaximumDecodeBHist tail)

private theorem RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMaximumToEventFlow : RegularCauchyMaximumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMaximumUp.mk X Y WX WY D S A U R E H C P N =>
      [[BMark.b0],
        regularCauchyMaximumEncodeBHist X,
        [BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist WX,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist WY,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyMaximumEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMaximumEncodeBHist N]

private def regularCauchyMaximumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMaximumEventAtDefault index rest

def regularCauchyMaximumFromEventFlow (ef : EventFlow) : Option RegularCauchyMaximumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMaximumUp.mk
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 1 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 3 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 5 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 7 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 9 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 11 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 13 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 15 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 17 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 19 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 21 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 23 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 25 ef))
      (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEventAtDefault 27 ef)))

private theorem RegularCauchyMaximumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyMaximumUp,
      regularCauchyMaximumFromEventFlow (regularCauchyMaximumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y WX WY D S A U R E H C P N =>
      change
        some
          (RegularCauchyMaximumUp.mk
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist X))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist Y))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist WX))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist WY))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist D))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist S))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist A))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist U))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist R))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist E))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist H))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist C))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist P))
            (regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist N))) =
          some (RegularCauchyMaximumUp.mk X Y WX WY D S A U R E H C P N)
      rw [RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode X,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode Y,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode WX,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode WY,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode U,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyMaximumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyMaximumUp} :
    regularCauchyMaximumToEventFlow x = regularCauchyMaximumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMaximumFromEventFlow (regularCauchyMaximumToEventFlow x) =
        regularCauchyMaximumFromEventFlow (regularCauchyMaximumToEventFlow y) :=
    congrArg regularCauchyMaximumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyMaximumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyMaximumTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMaximumBHistCarrier : BHistCarrier RegularCauchyMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMaximumToEventFlow
  fromEventFlow := regularCauchyMaximumFromEventFlow

instance regularCauchyMaximumChapterTasteGate : ChapterTasteGate RegularCauchyMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMaximumFromEventFlow (regularCauchyMaximumToEventFlow x) = some x
    exact RegularCauchyMaximumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyMaximumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyMaximumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMaximumChapterTasteGate

theorem RegularCauchyMaximumTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyMaximumDecodeBHist (regularCauchyMaximumEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMaximumUp,
        regularCauchyMaximumFromEventFlow (regularCauchyMaximumToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyMaximumUp,
          regularCauchyMaximumToEventFlow x = regularCauchyMaximumToEventFlow y → x = y) ∧
          regularCauchyMaximumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyMaximumTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyMaximumTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularCauchyMaximumTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyMaximumUp
