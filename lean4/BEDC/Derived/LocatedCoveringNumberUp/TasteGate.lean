import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCoveringNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCoveringNumberUp : Type where
  | mk (M Q T E B W H C P N : BHist) : LocatedCoveringNumberUp
  deriving DecidableEq

def locatedCoveringNumberEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCoveringNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCoveringNumberEncodeBHist h

def locatedCoveringNumberDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCoveringNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCoveringNumberDecodeBHist tail)

private theorem LocatedCoveringNumberTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCoveringNumberFields : LocatedCoveringNumberUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCoveringNumberUp.mk M Q T E B W H C P N => [M, Q, T, E, B, W, H, C, P, N]

def locatedCoveringNumberToEventFlow : LocatedCoveringNumberUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCoveringNumberFields x).map locatedCoveringNumberEncodeBHist

private def locatedCoveringNumberRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCoveringNumberRawAt index rest

def locatedCoveringNumberFromEventFlow (flow : EventFlow) : Option LocatedCoveringNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCoveringNumberUp.mk
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 0 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 1 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 2 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 3 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 4 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 5 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 6 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 7 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 8 flow))
      (locatedCoveringNumberDecodeBHist (locatedCoveringNumberRawAt 9 flow)))

private theorem LocatedCoveringNumberTasteGate_single_carrier_alignment_round_trip :
    forall x : LocatedCoveringNumberUp,
      locatedCoveringNumberFromEventFlow (locatedCoveringNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M Q T E B W H C P N =>
      change
        some
          (LocatedCoveringNumberUp.mk
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist M))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist Q))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist T))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist E))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist B))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist W))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist H))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist C))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist P))
            (locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist N))) =
          some (LocatedCoveringNumberUp.mk M Q T E B W H C P N)
      rw [LocatedCoveringNumberTasteGate_single_carrier_alignment_decode M,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode Q,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode T,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode E,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode B,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode W,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode H,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode C,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode P,
        LocatedCoveringNumberTasteGate_single_carrier_alignment_decode N]

private theorem locatedCoveringNumberToEventFlow_injective {x y : LocatedCoveringNumberUp} :
    locatedCoveringNumberToEventFlow x = locatedCoveringNumberToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCoveringNumberFromEventFlow (locatedCoveringNumberToEventFlow x) =
        locatedCoveringNumberFromEventFlow (locatedCoveringNumberToEventFlow y) :=
    congrArg locatedCoveringNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCoveringNumberTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedCoveringNumberTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCoveringNumberBHistCarrier : BHistCarrier LocatedCoveringNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCoveringNumberToEventFlow
  fromEventFlow := locatedCoveringNumberFromEventFlow

instance locatedCoveringNumberChapterTasteGate : ChapterTasteGate LocatedCoveringNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCoveringNumberFromEventFlow (locatedCoveringNumberToEventFlow x) = some x
    exact LocatedCoveringNumberTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCoveringNumberToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCoveringNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCoveringNumberChapterTasteGate

theorem LocatedCoveringNumberTasteGate_single_carrier_alignment :
    (forall h : BHist,
      locatedCoveringNumberDecodeBHist (locatedCoveringNumberEncodeBHist h) = h) ∧
      (forall x : LocatedCoveringNumberUp,
        locatedCoveringNumberFromEventFlow (locatedCoveringNumberToEventFlow x) = some x) ∧
      (forall x y : LocatedCoveringNumberUp,
        locatedCoveringNumberToEventFlow x = locatedCoveringNumberToEventFlow y -> x = y) ∧
      locatedCoveringNumberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedCoveringNumberTasteGate_single_carrier_alignment_decode,
      LocatedCoveringNumberTasteGate_single_carrier_alignment_round_trip,
      (fun _x _y heq => locatedCoveringNumberToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedCoveringNumberUp
