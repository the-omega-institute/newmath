import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactPolishSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactPolishSpaceUp : Type where
  | mk (K P C S W R H T Q N : BHist) : CompactPolishSpaceUp
  deriving DecidableEq

def compactPolishSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactPolishSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactPolishSpaceEncodeBHist h

def compactPolishSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactPolishSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactPolishSpaceDecodeBHist tail)

private theorem CompactPolishSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, compactPolishSpaceDecodeBHist
      (compactPolishSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactPolishSpaceFields : CompactPolishSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactPolishSpaceUp.mk K P C S W R H T Q N => [K, P, C, S, W, R, H, T, Q, N]

def compactPolishSpaceToEventFlow : CompactPolishSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactPolishSpaceFields x).map compactPolishSpaceEncodeBHist

private def compactPolishSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactPolishSpaceEventAtDefault index rest

def compactPolishSpaceFromEventFlow
    (ef : EventFlow) : Option CompactPolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactPolishSpaceUp.mk
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 0 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 1 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 2 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 3 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 4 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 5 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 6 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 7 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 8 ef))
      (compactPolishSpaceDecodeBHist (compactPolishSpaceEventAtDefault 9 ef)))

private theorem CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactPolishSpaceUp,
      compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K P C S W R H T Q N =>
      change
        some
          (CompactPolishSpaceUp.mk
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist K))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist P))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist C))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist S))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist W))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist R))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist H))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist T))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist Q))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist N))) =
          some (CompactPolishSpaceUp.mk K P C S W R H T Q N)
      rw [CompactPolishSpaceTasteGate_single_carrier_alignment_decode K,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode P,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode C,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode S,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode W,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode R,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode H,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode T,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode Q,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode N]

private theorem CompactPolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactPolishSpaceUp} :
    compactPolishSpaceToEventFlow x = compactPolishSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) =
        compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow y) :=
    congrArg compactPolishSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance compactPolishSpaceBHistCarrier :
    BHistCarrier CompactPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactPolishSpaceToEventFlow
  fromEventFlow := compactPolishSpaceFromEventFlow

instance compactPolishSpaceChapterTasteGate :
    ChapterTasteGate CompactPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) = some x
    exact CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactPolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactPolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactPolishSpaceChapterTasteGate

theorem CompactPolishSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactPolishSpaceUp) ∧
      (∀ h : BHist,
        compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist h) = h) ∧
        (∀ x : CompactPolishSpaceUp,
          compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) = some x) ∧
          (∀ x y : CompactPolishSpaceUp,
            compactPolishSpaceToEventFlow x = compactPolishSpaceToEventFlow y → x = y) ∧
            compactPolishSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨compactPolishSpaceChapterTasteGate⟩,
      CompactPolishSpaceTasteGate_single_carrier_alignment_decode,
      CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactPolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactPolishSpaceUp.TasteGate
