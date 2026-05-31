import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompleteMetricUp : Type where
  | mk (M S R Q W A C P N : BHist) : LocatedCompleteMetricUp
  deriving DecidableEq

def locatedCompleteMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompleteMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompleteMetricEncodeBHist h

def locatedCompleteMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompleteMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompleteMetricDecodeBHist tail)

private theorem LocatedCompleteMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompleteMetricFields : LocatedCompleteMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompleteMetricUp.mk M S R Q W A C P N => [M, S, R, Q, W, A, C, P, N]

def locatedCompleteMetricToEventFlow : LocatedCompleteMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCompleteMetricFields x).map locatedCompleteMetricEncodeBHist

private def locatedCompleteMetricRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompleteMetricRawAt index rest

def locatedCompleteMetricFromEventFlow (flow : EventFlow) : Option LocatedCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompleteMetricUp.mk
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 0 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 1 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 2 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 3 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 4 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 5 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 6 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 7 flow))
      (locatedCompleteMetricDecodeBHist (locatedCompleteMetricRawAt 8 flow)))

private theorem LocatedCompleteMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompleteMetricUp,
      locatedCompleteMetricFromEventFlow (locatedCompleteMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M S R Q W A C P N =>
      change
        some
          (LocatedCompleteMetricUp.mk
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist M))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist S))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist R))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist Q))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist W))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist A))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist C))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist P))
            (locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist N))) =
          some (LocatedCompleteMetricUp.mk M S R Q W A C P N)
      rw [LocatedCompleteMetricTasteGate_single_carrier_alignment_decode M,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode S,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode R,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode Q,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode W,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode A,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode C,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode P,
        LocatedCompleteMetricTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompleteMetricUp} :
    locatedCompleteMetricToEventFlow x = locatedCompleteMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompleteMetricFromEventFlow (locatedCompleteMetricToEventFlow x) =
        locatedCompleteMetricFromEventFlow (locatedCompleteMetricToEventFlow y) :=
    congrArg locatedCompleteMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCompleteMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedCompleteMetricTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCompleteMetricBHistCarrier : BHistCarrier LocatedCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompleteMetricToEventFlow
  fromEventFlow := locatedCompleteMetricFromEventFlow

instance locatedCompleteMetricChapterTasteGate :
    ChapterTasteGate LocatedCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompleteMetricFromEventFlow (locatedCompleteMetricToEventFlow x) = some x
    exact LocatedCompleteMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompleteMetricChapterTasteGate

theorem LocatedCompleteMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCompleteMetricDecodeBHist (locatedCompleteMetricEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedCompleteMetricUp) ∧
        Nonempty (ChapterTasteGate LocatedCompleteMetricUp) ∧
          locatedCompleteMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedCompleteMetricTasteGate_single_carrier_alignment_decode,
      ⟨locatedCompleteMetricBHistCarrier⟩,
      ⟨locatedCompleteMetricChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedCompleteMetricUp
