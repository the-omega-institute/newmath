import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalSupremumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalSupremumUp : Type where
  | mk (J U A B W R E H C P N : BHist) : LocatedIntervalSupremumUp
  deriving DecidableEq

def locatedIntervalSupremumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalSupremumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalSupremumEncodeBHist h

def locatedIntervalSupremumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalSupremumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalSupremumDecodeBHist tail)

private theorem locatedIntervalSupremumDecode_encode :
    ∀ h : BHist,
      locatedIntervalSupremumDecodeBHist
        (locatedIntervalSupremumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalSupremumFields : LocatedIntervalSupremumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalSupremumUp.mk J U A B W R E H C P N =>
      [J, U, A, B, W, R, E, H, C, P, N]

def locatedIntervalSupremumToEventFlow : LocatedIntervalSupremumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedIntervalSupremumFields x).map locatedIntervalSupremumEncodeBHist

private def locatedIntervalSupremumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalSupremumEventAt index rest

def locatedIntervalSupremumFromEventFlow (ef : EventFlow) :
    Option LocatedIntervalSupremumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalSupremumUp.mk
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 0 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 1 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 2 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 3 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 4 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 5 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 6 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 7 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 8 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 9 ef))
      (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEventAt 10 ef)))

private theorem locatedIntervalSupremum_round_trip :
    ∀ x : LocatedIntervalSupremumUp,
      locatedIntervalSupremumFromEventFlow
        (locatedIntervalSupremumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J U A B W R E H C P N =>
      change
        some
          (LocatedIntervalSupremumUp.mk
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist J))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist U))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist A))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist B))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist W))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist R))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist E))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist H))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist C))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist P))
            (locatedIntervalSupremumDecodeBHist (locatedIntervalSupremumEncodeBHist N))) =
          some (LocatedIntervalSupremumUp.mk J U A B W R E H C P N)
      rw [locatedIntervalSupremumDecode_encode J, locatedIntervalSupremumDecode_encode U,
        locatedIntervalSupremumDecode_encode A, locatedIntervalSupremumDecode_encode B,
        locatedIntervalSupremumDecode_encode W, locatedIntervalSupremumDecode_encode R,
        locatedIntervalSupremumDecode_encode E, locatedIntervalSupremumDecode_encode H,
        locatedIntervalSupremumDecode_encode C, locatedIntervalSupremumDecode_encode P,
        locatedIntervalSupremumDecode_encode N]

private theorem locatedIntervalSupremumToEventFlow_injective
    {x y : LocatedIntervalSupremumUp} :
    locatedIntervalSupremumToEventFlow x = locatedIntervalSupremumToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalSupremumFromEventFlow (locatedIntervalSupremumToEventFlow x) =
        locatedIntervalSupremumFromEventFlow (locatedIntervalSupremumToEventFlow y) :=
    congrArg locatedIntervalSupremumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedIntervalSupremum_round_trip x).symm
      (Eq.trans hread (locatedIntervalSupremum_round_trip y)))

instance locatedIntervalSupremumBHistCarrier : BHistCarrier LocatedIntervalSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalSupremumToEventFlow
  fromEventFlow := locatedIntervalSupremumFromEventFlow

instance locatedIntervalSupremumChapterTasteGate :
    ChapterTasteGate LocatedIntervalSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalSupremumFromEventFlow
        (locatedIntervalSupremumToEventFlow x) = some x
    exact locatedIntervalSupremum_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalSupremumToEventFlow_injective heq)

theorem LocatedIntervalSupremumTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LocatedIntervalSupremumUp) ∧
      Nonempty (ChapterTasteGate LocatedIntervalSupremumUp) ∧
        (∀ h : BHist,
          locatedIntervalSupremumDecodeBHist
            (locatedIntervalSupremumEncodeBHist h) = h) ∧
          (∀ x : LocatedIntervalSupremumUp,
            locatedIntervalSupremumFromEventFlow
              (locatedIntervalSupremumToEventFlow x) = some x) ∧
            (∀ x y : LocatedIntervalSupremumUp,
              locatedIntervalSupremumToEventFlow x =
                  locatedIntervalSupremumToEventFlow y →
                x = y) ∧
              locatedIntervalSupremumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨locatedIntervalSupremumBHistCarrier⟩,
      ⟨locatedIntervalSupremumChapterTasteGate⟩,
      locatedIntervalSupremumDecode_encode,
      locatedIntervalSupremum_round_trip,
      (fun _ _ heq => locatedIntervalSupremumToEventFlow_injective heq),
      rfl⟩

namespace TasteGate

theorem LocatedIntervalSupremumTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LocatedIntervalSupremumUp) ∧
      Nonempty (ChapterTasteGate LocatedIntervalSupremumUp) ∧
        (∀ h : BHist,
          locatedIntervalSupremumDecodeBHist
            (locatedIntervalSupremumEncodeBHist h) = h) ∧
          (∀ x : LocatedIntervalSupremumUp,
            locatedIntervalSupremumFromEventFlow
              (locatedIntervalSupremumToEventFlow x) = some x) ∧
            (∀ x y : LocatedIntervalSupremumUp,
              locatedIntervalSupremumToEventFlow x =
                  locatedIntervalSupremumToEventFlow y →
                x = y) ∧
              locatedIntervalSupremumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    _root_.BEDC.Derived.LocatedIntervalSupremumUp.LocatedIntervalSupremumTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.LocatedIntervalSupremumUp
