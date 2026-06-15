import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedFormalBarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedFormalBarUp : Type where
  | mk (F S B W Q R H C P N : BHist) : LocatedFormalBarUp
  deriving DecidableEq

def locatedFormalBarEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedFormalBarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedFormalBarEncodeBHist h

def locatedFormalBarDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedFormalBarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedFormalBarDecodeBHist tail)

private theorem LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def locatedFormalBarFields : LocatedFormalBarUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedFormalBarUp.mk F S B W Q R H C P N => [F, S, B, W, Q, R, H, C, P, N]

private def locatedFormalBarToEventFlow : LocatedFormalBarUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedFormalBarFields x).map locatedFormalBarEncodeBHist

private def locatedFormalBarEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedFormalBarEventAt index rest

private def locatedFormalBarFromEventFlow (ef : EventFlow) : Option LocatedFormalBarUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedFormalBarUp.mk
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 0 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 1 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 2 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 3 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 4 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 5 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 6 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 7 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 8 ef))
      (locatedFormalBarDecodeBHist (locatedFormalBarEventAt 9 ef)))

private theorem LocatedFormalBarTasteGate_single_carrier_alignment_round_trip
    (x : LocatedFormalBarUp) :
    locatedFormalBarFromEventFlow (locatedFormalBarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F S B W Q R H C P N =>
      change
        some
          (LocatedFormalBarUp.mk
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist F))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist S))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist B))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist W))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist Q))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist R))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist H))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist C))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist P))
            (locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist N))) =
          some (LocatedFormalBarUp.mk F S B W Q R H C P N)
      rw [LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode F,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode S,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode B,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode W,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode R,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode H,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode C,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode P,
        LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode N]

private theorem locatedFormalBarToEventFlow_injective {x y : LocatedFormalBarUp} :
    locatedFormalBarToEventFlow x = locatedFormalBarToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedFormalBarFromEventFlow (locatedFormalBarToEventFlow x) =
        locatedFormalBarFromEventFlow (locatedFormalBarToEventFlow y) :=
    congrArg locatedFormalBarFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedFormalBarTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedFormalBarTasteGate_single_carrier_alignment_round_trip y)))

instance locatedFormalBarBHistCarrier : BHistCarrier LocatedFormalBarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedFormalBarToEventFlow
  fromEventFlow := locatedFormalBarFromEventFlow

instance locatedFormalBarChapterTasteGate : ChapterTasteGate LocatedFormalBarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedFormalBarFromEventFlow (locatedFormalBarToEventFlow x) = some x
    exact LocatedFormalBarTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedFormalBarToEventFlow_injective heq)

theorem LocatedFormalBarTasteGate_single_carrier_alignment :
    (forall h : BHist, locatedFormalBarDecodeBHist (locatedFormalBarEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedFormalBarUp) ∧
        Nonempty (ChapterTasteGate LocatedFormalBarUp) ∧
          locatedFormalBarEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedFormalBarTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨locatedFormalBarBHistCarrier⟩, ⟨locatedFormalBarChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.LocatedFormalBarUp
