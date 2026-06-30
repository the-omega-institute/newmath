import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalCompletionUp : Type where
  | mk (E0 E1 D W Q M R H C P N : BHist) : LocatedIntervalCompletionUp
  deriving DecidableEq

def locatedIntervalCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalCompletionEncodeBHist h

private def locatedIntervalCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalCompletionDecodeBHist tail)

private theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def locatedIntervalCompletionFields : LocatedIntervalCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalCompletionUp.mk E0 E1 D W Q M R H C P N =>
      [E0, E1, D, W, Q, M, R, H, C, P, N]

private def locatedIntervalCompletionToEventFlow : LocatedIntervalCompletionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedIntervalCompletionFields x).map locatedIntervalCompletionEncodeBHist

private def locatedIntervalCompletionRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalCompletionRawAt index rest

private def locatedIntervalCompletionFromEventFlow
    (flow : EventFlow) : Option LocatedIntervalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalCompletionUp.mk
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 0 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 1 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 2 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 3 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 4 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 5 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 6 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 7 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 8 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 9 flow))
      (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionRawAt 10 flow)))

private theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : LocatedIntervalCompletionUp,
      locatedIntervalCompletionFromEventFlow
        (locatedIntervalCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E0 E1 D W Q M R H C P N =>
      change
        some
          (LocatedIntervalCompletionUp.mk
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist E0))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist E1))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist D))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist W))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist Q))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist M))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist R))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist H))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist C))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist P))
            (locatedIntervalCompletionDecodeBHist (locatedIntervalCompletionEncodeBHist N))) =
          some (LocatedIntervalCompletionUp.mk E0 E1 D W Q M R H C P N)
      rw [LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode E0,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode E1,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode D,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode W,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode M,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode R,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode H,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode C,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode P,
        LocatedIntervalCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalCompletionUp} :
    locatedIntervalCompletionToEventFlow x = locatedIntervalCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow x) =
        locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow y) :=
    congrArg locatedIntervalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance locatedIntervalCompletionBHistCarrier :
    BHistCarrier LocatedIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalCompletionToEventFlow
  fromEventFlow := locatedIntervalCompletionFromEventFlow

instance locatedIntervalCompletionChapterTasteGate :
    ChapterTasteGate LocatedIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalCompletionFromEventFlow (locatedIntervalCompletionToEventFlow x) =
        some x
    exact LocatedIntervalCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedIntervalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedIntervalCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LocatedIntervalCompletionUp) ∧
      Nonempty (ChapterTasteGate LocatedIntervalCompletionUp) ∧
        locatedIntervalCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨locatedIntervalCompletionBHistCarrier⟩,
      ⟨locatedIntervalCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedIntervalCompletionUp.TasteGate
