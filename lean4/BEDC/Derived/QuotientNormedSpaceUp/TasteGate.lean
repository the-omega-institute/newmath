import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuotientNormedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuotientNormedSpaceUp : Type where
  | mk (E S Q N M H C P L : BHist) : QuotientNormedSpaceUp
  deriving DecidableEq

def quotientNormedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 tail => BMark.b0 :: quotientNormedSpaceEncodeBHist tail
  | BHist.e1 tail => BMark.b1 :: quotientNormedSpaceEncodeBHist tail

def quotientNormedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quotientNormedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quotientNormedSpaceDecodeBHist tail)

private theorem QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ row : BHist,
      quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist row) = row := by
  -- BEDC touchpoint anchor: BHist BMark
  intro row
  induction row with
  | Empty => rfl
  | e0 row ih => exact congrArg BHist.e0 ih
  | e1 row ih => exact congrArg BHist.e1 ih

def quotientNormedSpaceToEventFlow : QuotientNormedSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | QuotientNormedSpaceUp.mk E S Q N M H C P L =>
      [quotientNormedSpaceEncodeBHist E,
        quotientNormedSpaceEncodeBHist S,
        quotientNormedSpaceEncodeBHist Q,
        quotientNormedSpaceEncodeBHist N,
        quotientNormedSpaceEncodeBHist M,
        quotientNormedSpaceEncodeBHist H,
        quotientNormedSpaceEncodeBHist C,
        quotientNormedSpaceEncodeBHist P,
        quotientNormedSpaceEncodeBHist L]

private def quotientNormedSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => quotientNormedSpaceEventAtDefault index rest

def quotientNormedSpaceFromEventFlow (flow : EventFlow) : Option QuotientNormedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (QuotientNormedSpaceUp.mk
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 0 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 1 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 2 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 3 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 4 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 5 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 6 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 7 flow))
      (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEventAtDefault 8 flow)))

private theorem QuotientNormedSpaceTasteGate_single_carrier_alignment_round_trip
    (x : QuotientNormedSpaceUp) :
    quotientNormedSpaceFromEventFlow (quotientNormedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E S Q N M H C P L =>
      change
        some
          (QuotientNormedSpaceUp.mk
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist E))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist S))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist Q))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist N))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist M))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist H))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist C))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist P))
            (quotientNormedSpaceDecodeBHist (quotientNormedSpaceEncodeBHist L))) =
          some (QuotientNormedSpaceUp.mk E S Q N M H C P L)
      rw [QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode E,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode S,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode N,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode M,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode H,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode C,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode P,
        QuotientNormedSpaceTasteGate_single_carrier_alignment_decode_encode L]

private theorem QuotientNormedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : QuotientNormedSpaceUp} :
    quotientNormedSpaceToEventFlow x = quotientNormedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quotientNormedSpaceFromEventFlow (quotientNormedSpaceToEventFlow x) =
        quotientNormedSpaceFromEventFlow (quotientNormedSpaceToEventFlow y) :=
    congrArg quotientNormedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (QuotientNormedSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (QuotientNormedSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance quotientNormedSpaceBHistCarrier : BHistCarrier QuotientNormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quotientNormedSpaceToEventFlow
  fromEventFlow := quotientNormedSpaceFromEventFlow

instance quotientNormedSpaceChapterTasteGate :
    ChapterTasteGate QuotientNormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quotientNormedSpaceFromEventFlow (quotientNormedSpaceToEventFlow x) = some x
    exact QuotientNormedSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (QuotientNormedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem QuotientNormedSpaceTasteGate_single_carrier_alignment :
    ChapterTasteGate QuotientNormedSpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact quotientNormedSpaceChapterTasteGate

end BEDC.Derived.QuotientNormedSpaceUp
