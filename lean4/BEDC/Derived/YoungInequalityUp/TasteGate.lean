import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YoungInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YoungInequalityUp : Type where
  | mk (A B E R S V M D F H C P N : BHist) : YoungInequalityUp
  deriving DecidableEq

def youngInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: youngInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: youngInequalityEncodeBHist h

def youngInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (youngInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (youngInequalityDecodeBHist tail)

private theorem YoungInequalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, youngInequalityDecodeBHist (youngInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def youngInequalityFields : YoungInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YoungInequalityUp.mk A B E R S V M D F H C P N => [A, B, E, R, S, V, M, D, F, H, C, P, N]

def youngInequalityToEventFlow : YoungInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (youngInequalityFields x).map youngInequalityEncodeBHist

private def YoungInequalityTasteGate_single_carrier_alignment_event_at_default :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      YoungInequalityTasteGate_single_carrier_alignment_event_at_default index rest

def youngInequalityFromEventFlow : EventFlow → Option YoungInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (YoungInequalityUp.mk
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 0 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 1 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 2 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 3 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 4 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 5 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 6 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 7 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 8 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 9 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 10 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 11 ef))
        (youngInequalityDecodeBHist
          (YoungInequalityTasteGate_single_carrier_alignment_event_at_default 12 ef)))

private theorem YoungInequalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : YoungInequalityUp,
      youngInequalityFromEventFlow (youngInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B E R S V M D F H C P N =>
      change
        some
          (YoungInequalityUp.mk
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist A))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist B))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist E))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist R))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist S))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist V))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist M))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist D))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist F))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist H))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist C))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist P))
            (youngInequalityDecodeBHist (youngInequalityEncodeBHist N))) =
          some (YoungInequalityUp.mk A B E R S V M D F H C P N)
      rw [YoungInequalityTasteGate_single_carrier_alignment_decode_encode A,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode B,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode E,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode R,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode S,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode V,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode M,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode D,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode F,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode H,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode C,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode P,
        YoungInequalityTasteGate_single_carrier_alignment_decode_encode N]

private theorem YoungInequalityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : YoungInequalityUp} :
    youngInequalityToEventFlow x = youngInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      youngInequalityFromEventFlow (youngInequalityToEventFlow x) =
        youngInequalityFromEventFlow (youngInequalityToEventFlow y) :=
    congrArg youngInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (YoungInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (YoungInequalityTasteGate_single_carrier_alignment_round_trip y)))

instance youngInequalityBHistCarrier : BHistCarrier YoungInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := youngInequalityToEventFlow
  fromEventFlow := youngInequalityFromEventFlow

instance youngInequalityChapterTasteGate : ChapterTasteGate YoungInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change youngInequalityFromEventFlow (youngInequalityToEventFlow x) = some x
    exact YoungInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (YoungInequalityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate YoungInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  youngInequalityChapterTasteGate

theorem YoungInequalityTasteGate_single_carrier_alignment :
    youngInequalityEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      Nonempty (BEDC.Meta.TasteGate.BHistCarrier YoungInequalityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate YoungInequalityUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨rfl, ⟨youngInequalityBHistCarrier⟩, ⟨youngInequalityChapterTasteGate⟩⟩

end BEDC.Derived.YoungInequalityUp
