import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealBisectionSearchUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealBisectionSearchUp : Type where
  | mk (I B F D Q W R H C P N : BHist) : LocatedRealBisectionSearchUp
  deriving DecidableEq

def locatedRealBisectionSearchEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealBisectionSearchEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealBisectionSearchEncodeBHist h

def locatedRealBisectionSearchDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealBisectionSearchDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealBisectionSearchDecodeBHist tail)

private theorem LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealBisectionSearchFields : LocatedRealBisectionSearchUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealBisectionSearchUp.mk I B F D Q W R H C P N =>
      [I, B, F, D, Q, W, R, H, C, P, N]

def locatedRealBisectionSearchToEventFlow : LocatedRealBisectionSearchUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedRealBisectionSearchFields x).map locatedRealBisectionSearchEncodeBHist

private def locatedRealBisectionSearchRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealBisectionSearchRawAt index rest

def locatedRealBisectionSearchFromEventFlow
    (flow : EventFlow) : Option LocatedRealBisectionSearchUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealBisectionSearchUp.mk
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 0 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 1 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 2 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 3 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 4 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 5 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 6 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 7 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 8 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 9 flow))
      (locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchRawAt 10 flow)))

private theorem LocatedRealBisectionSearchTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealBisectionSearchUp,
      locatedRealBisectionSearchFromEventFlow
          (locatedRealBisectionSearchToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I B F D Q W R H C P N =>
      change
        some
          (LocatedRealBisectionSearchUp.mk
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist I))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist B))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist F))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist D))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist Q))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist W))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist R))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist H))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist C))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist P))
            (locatedRealBisectionSearchDecodeBHist
              (locatedRealBisectionSearchEncodeBHist N))) =
          some (LocatedRealBisectionSearchUp.mk I B F D Q W R H C P N)
      rw [LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode I,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode B,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode F,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode D,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode Q,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode W,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode R,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode H,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode C,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode P,
        LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode N]

private theorem locatedRealBisectionSearchToEventFlow_injective
    {x y : LocatedRealBisectionSearchUp} :
    locatedRealBisectionSearchToEventFlow x = locatedRealBisectionSearchToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealBisectionSearchFromEventFlow (locatedRealBisectionSearchToEventFlow x) =
        locatedRealBisectionSearchFromEventFlow (locatedRealBisectionSearchToEventFlow y) :=
    congrArg locatedRealBisectionSearchFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealBisectionSearchTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealBisectionSearchTasteGate_single_carrier_alignment_round_trip y)))

instance locatedRealBisectionSearchBHistCarrier :
    BHistCarrier LocatedRealBisectionSearchUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealBisectionSearchToEventFlow
  fromEventFlow := locatedRealBisectionSearchFromEventFlow

instance locatedRealBisectionSearchChapterTasteGate :
    ChapterTasteGate LocatedRealBisectionSearchUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealBisectionSearchFromEventFlow
          (locatedRealBisectionSearchToEventFlow x) =
        some x
    exact LocatedRealBisectionSearchTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealBisectionSearchToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealBisectionSearchUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealBisectionSearchChapterTasteGate

theorem LocatedRealBisectionSearchTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealBisectionSearchDecodeBHist (locatedRealBisectionSearchEncodeBHist h) = h) ∧
      (∀ x : LocatedRealBisectionSearchUp,
        locatedRealBisectionSearchFromEventFlow (locatedRealBisectionSearchToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedRealBisectionSearchUp,
          locatedRealBisectionSearchToEventFlow x =
              locatedRealBisectionSearchToEventFlow y →
            x = y) ∧
          locatedRealBisectionSearchEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedRealBisectionSearchTasteGate_single_carrier_alignment_decode,
      LocatedRealBisectionSearchTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => locatedRealBisectionSearchToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedRealBisectionSearchUp
