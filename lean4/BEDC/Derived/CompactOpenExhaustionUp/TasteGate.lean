import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOpenExhaustionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactOpenExhaustionUp : Type where
  | mk (K O F S W R E H C P N : BHist) : CompactOpenExhaustionUp
  deriving DecidableEq

def compactOpenExhaustionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOpenExhaustionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOpenExhaustionEncodeBHist h

def compactOpenExhaustionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOpenExhaustionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOpenExhaustionDecodeBHist tail)

private theorem compactOpenExhaustion_decode_encode :
    ∀ h : BHist,
      compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactOpenExhaustionFields : CompactOpenExhaustionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOpenExhaustionUp.mk K O F S W R E H C P N =>
      [K, O, F, S, W, R, E, H, C, P, N]

def compactOpenExhaustionToEventFlow : CompactOpenExhaustionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map compactOpenExhaustionEncodeBHist (compactOpenExhaustionFields x)

private def compactOpenExhaustionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactOpenExhaustionRawAt index rest

def compactOpenExhaustionFromEventFlow
    (flow : EventFlow) : Option CompactOpenExhaustionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactOpenExhaustionUp.mk
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 0 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 1 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 2 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 3 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 4 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 5 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 6 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 7 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 8 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 9 flow))
      (compactOpenExhaustionDecodeBHist (compactOpenExhaustionRawAt 10 flow)))

private theorem compactOpenExhaustion_round_trip :
    ∀ x : CompactOpenExhaustionUp,
      compactOpenExhaustionFromEventFlow (compactOpenExhaustionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K O F S W R E H C P N =>
      change
        some
          (CompactOpenExhaustionUp.mk
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist K))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist O))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist F))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist S))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist W))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist R))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist E))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist H))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist C))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist P))
            (compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist N))) =
          some (CompactOpenExhaustionUp.mk K O F S W R E H C P N)
      rw [compactOpenExhaustion_decode_encode K,
        compactOpenExhaustion_decode_encode O,
        compactOpenExhaustion_decode_encode F,
        compactOpenExhaustion_decode_encode S,
        compactOpenExhaustion_decode_encode W,
        compactOpenExhaustion_decode_encode R,
        compactOpenExhaustion_decode_encode E,
        compactOpenExhaustion_decode_encode H,
        compactOpenExhaustion_decode_encode C,
        compactOpenExhaustion_decode_encode P,
        compactOpenExhaustion_decode_encode N]

private theorem compactOpenExhaustionToEventFlow_injective
    {x y : CompactOpenExhaustionUp} :
    compactOpenExhaustionToEventFlow x = compactOpenExhaustionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactOpenExhaustionFromEventFlow (compactOpenExhaustionToEventFlow x) =
        compactOpenExhaustionFromEventFlow (compactOpenExhaustionToEventFlow y) :=
    congrArg compactOpenExhaustionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactOpenExhaustion_round_trip x).symm
      (Eq.trans hread (compactOpenExhaustion_round_trip y)))

instance compactOpenExhaustionBHistCarrier :
    BHistCarrier CompactOpenExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOpenExhaustionToEventFlow
  fromEventFlow := compactOpenExhaustionFromEventFlow

instance compactOpenExhaustionChapterTasteGate :
    ChapterTasteGate CompactOpenExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactOpenExhaustionFromEventFlow (compactOpenExhaustionToEventFlow x) = some x
    exact compactOpenExhaustion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactOpenExhaustionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactOpenExhaustionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactOpenExhaustionChapterTasteGate

theorem CompactOpenExhaustionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompactOpenExhaustionUp) ∧
      Nonempty (ChapterTasteGate CompactOpenExhaustionUp) ∧
        (∀ h : BHist,
          compactOpenExhaustionDecodeBHist (compactOpenExhaustionEncodeBHist h) = h) ∧
          compactOpenExhaustionEncodeBHist BHist.Empty = ([] : List BMark) ∧
            compactOpenExhaustionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨compactOpenExhaustionBHistCarrier⟩,
      ⟨compactOpenExhaustionChapterTasteGate⟩,
      compactOpenExhaustion_decode_encode,
      rfl,
      rfl⟩

end BEDC.Derived.CompactOpenExhaustionUp.TasteGate
