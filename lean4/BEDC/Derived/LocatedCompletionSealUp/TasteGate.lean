import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionSealUp : Type where
  | mk (D S R Q E A T H C P N : BHist) : LocatedCompletionSealUp
  deriving DecidableEq

def locatedCompletionSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionSealEncodeBHist h

def locatedCompletionSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionSealDecodeBHist tail)

private theorem LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionSealFields : LocatedCompletionSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionSealUp.mk D S R Q E A T H C P N =>
      [D, S, R, Q, E, A, T, H, C, P, N]

def locatedCompletionSealToEventFlow : LocatedCompletionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map locatedCompletionSealEncodeBHist (locatedCompletionSealFields x)

private def locatedCompletionSealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompletionSealRawAt index rest

def locatedCompletionSealFromEventFlow : EventFlow → Option LocatedCompletionSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (LocatedCompletionSealUp.mk
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 0 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 1 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 2 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 3 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 4 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 5 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 6 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 7 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 8 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 9 flow))
          (locatedCompletionSealDecodeBHist (locatedCompletionSealRawAt 10 flow)))

private theorem LocatedCompletionSealUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompletionSealUp,
      locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R Q E A T H C P N =>
      change
        some
          (LocatedCompletionSealUp.mk
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist D))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist S))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist R))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist Q))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist E))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist A))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist T))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist H))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist C))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist P))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist N))) =
          some (LocatedCompletionSealUp.mk D S R Q E A T H C P N)
      rw [LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode D,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode S,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode R,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode Q,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode E,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode A,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode T,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode H,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode C,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode P,
        LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCompletionSealUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompletionSealUp} :
    locatedCompletionSealToEventFlow x = locatedCompletionSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) =
        locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow y) :=
    congrArg locatedCompletionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCompletionSealUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedCompletionSealUpTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCompletionSealBHistCarrier : BHistCarrier LocatedCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionSealToEventFlow
  fromEventFlow := locatedCompletionSealFromEventFlow

instance locatedCompletionSealChapterTasteGate : ChapterTasteGate LocatedCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) = some x
    exact LocatedCompletionSealUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCompletionSealUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedCompletionSealUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist h) = h) ∧
      (∀ x : LocatedCompletionSealUp,
        locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) = some x) ∧
        (∀ x y : LocatedCompletionSealUp,
          locatedCompletionSealToEventFlow x = locatedCompletionSealToEventFlow y → x = y) ∧
          locatedCompletionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedCompletionSealUpTasteGate_single_carrier_alignment_decode,
      LocatedCompletionSealUpTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact LocatedCompletionSealUpTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedCompletionSealUp
