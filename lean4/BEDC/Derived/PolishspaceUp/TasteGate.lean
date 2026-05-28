import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolishSpaceUp : Type where
  | mk (M K D S R W H C G N : BHist) : PolishSpaceUp
  deriving DecidableEq

def polishSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: polishSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: polishSpaceEncodeBHist h

def polishSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (polishSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (polishSpaceDecodeBHist tail)

private theorem PolishSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, polishSpaceDecodeBHist (polishSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def polishSpaceFields : PolishSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PolishSpaceUp.mk M K D S R W H C G N => [M, K, D, S, R, W, H, C, G, N]

def polishSpaceToEventFlow : PolishSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (polishSpaceFields token).map polishSpaceEncodeBHist

private def polishSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => polishSpaceEventAtDefault index rest

def polishSpaceFromEventFlow (ef : EventFlow) : Option PolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PolishSpaceUp.mk
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 0 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 1 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 2 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 3 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 4 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 5 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 6 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 7 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 8 ef))
      (polishSpaceDecodeBHist (polishSpaceEventAtDefault 9 ef)))

private theorem PolishSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PolishSpaceUp,
      polishSpaceFromEventFlow (polishSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M K D S R W H C G N =>
      change
        some
          (PolishSpaceUp.mk
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist M))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist K))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist D))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist S))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist R))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist W))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist H))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist C))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist G))
            (polishSpaceDecodeBHist (polishSpaceEncodeBHist N))) =
          some (PolishSpaceUp.mk M K D S R W H C G N)
      rw [PolishSpaceTasteGate_single_carrier_alignment_decode M,
        PolishSpaceTasteGate_single_carrier_alignment_decode K,
        PolishSpaceTasteGate_single_carrier_alignment_decode D,
        PolishSpaceTasteGate_single_carrier_alignment_decode S,
        PolishSpaceTasteGate_single_carrier_alignment_decode R,
        PolishSpaceTasteGate_single_carrier_alignment_decode W,
        PolishSpaceTasteGate_single_carrier_alignment_decode H,
        PolishSpaceTasteGate_single_carrier_alignment_decode C,
        PolishSpaceTasteGate_single_carrier_alignment_decode G,
        PolishSpaceTasteGate_single_carrier_alignment_decode N]

private theorem PolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PolishSpaceUp} :
    polishSpaceToEventFlow x = polishSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      polishSpaceFromEventFlow (polishSpaceToEventFlow x) =
        polishSpaceFromEventFlow (polishSpaceToEventFlow y) :=
    congrArg polishSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PolishSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PolishSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance polishSpaceBHistCarrier : BHistCarrier PolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := polishSpaceToEventFlow
  fromEventFlow := polishSpaceFromEventFlow

instance polishSpaceChapterTasteGate : ChapterTasteGate PolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change polishSpaceFromEventFlow (polishSpaceToEventFlow x) = some x
    exact PolishSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PolishSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, polishSpaceDecodeBHist (polishSpaceEncodeBHist h) = h) ∧
      (∀ x : PolishSpaceUp, polishSpaceFromEventFlow (polishSpaceToEventFlow x) = some x) ∧
        (∀ x y : PolishSpaceUp,
          polishSpaceToEventFlow x = polishSpaceToEventFlow y → x = y) ∧
          polishSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PolishSpaceTasteGate_single_carrier_alignment_decode,
      PolishSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PolishSpaceUp
