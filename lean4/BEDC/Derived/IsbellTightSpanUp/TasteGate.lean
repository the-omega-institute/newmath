import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IsbellTightSpanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IsbellTightSpanUp : Type where
  | mk (M F E O S Q L R H C P N : BHist) : IsbellTightSpanUp
  deriving DecidableEq

def isbellTightSpanEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: isbellTightSpanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: isbellTightSpanEncodeBHist h

def isbellTightSpanDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (isbellTightSpanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (isbellTightSpanDecodeBHist tail)

private theorem IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def isbellTightSpanFields : IsbellTightSpanUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IsbellTightSpanUp.mk M F E O S Q L R H C P N => [M, F, E, O, S, Q, L, R, H, C, P, N]

def isbellTightSpanToEventFlow : IsbellTightSpanUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (isbellTightSpanFields x).map isbellTightSpanEncodeBHist

private def IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default index rest

def isbellTightSpanFromEventFlow : EventFlow → Option IsbellTightSpanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (IsbellTightSpanUp.mk
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 0 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 1 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 2 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 3 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 4 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 5 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 6 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 7 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 8 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 9 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 10 ef))
        (isbellTightSpanDecodeBHist
          (IsbellTightSpanTasteGate_single_carrier_alignment_event_at_default 11 ef)))

private theorem IsbellTightSpanTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IsbellTightSpanUp,
      isbellTightSpanFromEventFlow (isbellTightSpanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F E O S Q L R H C P N =>
      change
        some
          (IsbellTightSpanUp.mk
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist M))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist F))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist E))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist O))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist S))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist Q))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist L))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist R))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist H))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist C))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist P))
            (isbellTightSpanDecodeBHist (isbellTightSpanEncodeBHist N))) =
          some (IsbellTightSpanUp.mk M F E O S Q L R H C P N)
      rw [IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode M,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode F,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode E,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode O,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode S,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode Q,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode L,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode R,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode H,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode C,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode P,
        IsbellTightSpanTasteGate_single_carrier_alignment_decode_encode N]

private theorem IsbellTightSpanTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IsbellTightSpanUp} :
    isbellTightSpanToEventFlow x = isbellTightSpanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      isbellTightSpanFromEventFlow (isbellTightSpanToEventFlow x) =
        isbellTightSpanFromEventFlow (isbellTightSpanToEventFlow y) :=
    congrArg isbellTightSpanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IsbellTightSpanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IsbellTightSpanTasteGate_single_carrier_alignment_round_trip y)))

instance isbellTightSpanBHistCarrier : BHistCarrier IsbellTightSpanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := isbellTightSpanToEventFlow
  fromEventFlow := isbellTightSpanFromEventFlow

instance isbellTightSpanChapterTasteGate : ChapterTasteGate IsbellTightSpanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change isbellTightSpanFromEventFlow (isbellTightSpanToEventFlow x) = some x
    exact IsbellTightSpanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IsbellTightSpanTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate IsbellTightSpanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  isbellTightSpanChapterTasteGate

theorem IsbellTightSpanTasteGate_single_carrier_alignment :
    isbellTightSpanEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      Nonempty (BEDC.Meta.TasteGate.BHistCarrier IsbellTightSpanUp) ∧
        Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate IsbellTightSpanUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨rfl, ⟨isbellTightSpanBHistCarrier⟩, ⟨isbellTightSpanChapterTasteGate⟩⟩

end BEDC.Derived.IsbellTightSpanUp
