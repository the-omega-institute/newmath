import BEDC.Derived.BishopIntervalEnclosureUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalEnclosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def bishopIntervalEnclosureEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalEnclosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalEnclosureEncodeBHist h

def bishopIntervalEnclosureDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalEnclosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalEnclosureDecodeBHist tail)

private theorem bishopIntervalEnclosure_decode_encode_bhist :
    forall h : BHist,
      bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopIntervalEnclosureFields :
    BishopIntervalEnclosureUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalEnclosureUp.mk L U Q D R S H C P N =>
      [L, U, Q, D, R, S, H, C, P, N]

def bishopIntervalEnclosureToEventFlow :
    BishopIntervalEnclosureUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopIntervalEnclosureFields x).map
        bishopIntervalEnclosureEncodeBHist

private def bishopIntervalEnclosureEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopIntervalEnclosureEventAtDefault index rest

def bishopIntervalEnclosureFromEventFlow
    (flow : EventFlow) : Option BishopIntervalEnclosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopIntervalEnclosureUp.mk
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 0 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 1 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 2 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 3 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 4 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 5 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 6 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 7 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 8 flow))
      (bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEventAtDefault 9 flow)))

private theorem bishopIntervalEnclosure_round_trip :
    forall x : BishopIntervalEnclosureUp,
      bishopIntervalEnclosureFromEventFlow
        (bishopIntervalEnclosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U Q D R S H C P N =>
      change
        some
          (BishopIntervalEnclosureUp.mk
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist L))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist U))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist Q))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist D))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist R))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist S))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist H))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist C))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist P))
            (bishopIntervalEnclosureDecodeBHist
              (bishopIntervalEnclosureEncodeBHist N))) =
          some (BishopIntervalEnclosureUp.mk L U Q D R S H C P N)
      rw [bishopIntervalEnclosure_decode_encode_bhist L,
        bishopIntervalEnclosure_decode_encode_bhist U,
        bishopIntervalEnclosure_decode_encode_bhist Q,
        bishopIntervalEnclosure_decode_encode_bhist D,
        bishopIntervalEnclosure_decode_encode_bhist R,
        bishopIntervalEnclosure_decode_encode_bhist S,
        bishopIntervalEnclosure_decode_encode_bhist H,
        bishopIntervalEnclosure_decode_encode_bhist C,
        bishopIntervalEnclosure_decode_encode_bhist P,
        bishopIntervalEnclosure_decode_encode_bhist N]

private theorem BishopIntervalEnclosureToEventFlow_injective
    {x y : BishopIntervalEnclosureUp} :
    bishopIntervalEnclosureToEventFlow x =
      bishopIntervalEnclosureToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalEnclosureFromEventFlow
          (bishopIntervalEnclosureToEventFlow x) =
        bishopIntervalEnclosureFromEventFlow
          (bishopIntervalEnclosureToEventFlow y) :=
    congrArg bishopIntervalEnclosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopIntervalEnclosure_round_trip x).symm
      (Eq.trans hread (bishopIntervalEnclosure_round_trip y)))

instance bishopIntervalEnclosureBHistCarrier :
    BHistCarrier BishopIntervalEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalEnclosureToEventFlow
  fromEventFlow := bishopIntervalEnclosureFromEventFlow

instance bishopIntervalEnclosureChapterTasteGate :
    ChapterTasteGate BishopIntervalEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopIntervalEnclosureFromEventFlow
        (bishopIntervalEnclosureToEventFlow x) = some x
    exact bishopIntervalEnclosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopIntervalEnclosureToEventFlow_injective heq)

theorem BishopIntervalEnclosureTasteGate_single_carrier_alignment :
    (forall h : BHist,
      bishopIntervalEnclosureDecodeBHist
        (bishopIntervalEnclosureEncodeBHist h) = h) /\
      (forall x : BishopIntervalEnclosureUp,
        bishopIntervalEnclosureFromEventFlow
          (bishopIntervalEnclosureToEventFlow x) = some x) /\
        (forall x y : BishopIntervalEnclosureUp,
          bishopIntervalEnclosureToEventFlow x =
            bishopIntervalEnclosureToEventFlow y -> x = y) /\
          bishopIntervalEnclosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bishopIntervalEnclosure_decode_encode_bhist,
      bishopIntervalEnclosure_round_trip,
      (fun _ _ heq => BishopIntervalEnclosureToEventFlow_injective heq), rfl⟩

end BEDC.Derived.BishopIntervalEnclosureUp
