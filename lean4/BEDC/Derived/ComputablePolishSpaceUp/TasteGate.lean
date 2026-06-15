import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ComputablePolishSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ComputablePolishSpaceUp : Type where
  | mk (P E R A Q S G D L H K U N : BHist) : ComputablePolishSpaceUp
  deriving DecidableEq

def computablePolishSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: computablePolishSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: computablePolishSpaceEncodeBHist h

def computablePolishSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (computablePolishSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (computablePolishSpaceDecodeBHist tail)

private theorem ComputablePolishSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def computablePolishSpaceFields : ComputablePolishSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ComputablePolishSpaceUp.mk P E R A Q S G D L H K U N =>
      [P, E, R, A, Q, S, G, D, L, H, K, U, N]

def computablePolishSpaceToEventFlow : ComputablePolishSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (computablePolishSpaceFields token).map computablePolishSpaceEncodeBHist

private def computablePolishSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => computablePolishSpaceEventAtDefault index rest

def computablePolishSpaceFromEventFlow (ef : EventFlow) : Option ComputablePolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ComputablePolishSpaceUp.mk
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 0 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 1 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 2 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 3 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 4 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 5 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 6 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 7 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 8 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 9 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 10 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 11 ef))
      (computablePolishSpaceDecodeBHist (computablePolishSpaceEventAtDefault 12 ef)))

private theorem ComputablePolishSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ComputablePolishSpaceUp,
      computablePolishSpaceFromEventFlow (computablePolishSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk P E R A Q S G D L H K U N =>
      change
        some
          (ComputablePolishSpaceUp.mk
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist P))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist E))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist R))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist A))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist Q))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist S))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist G))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist D))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist L))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist H))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist K))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist U))
            (computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist N))) =
          some (ComputablePolishSpaceUp.mk P E R A Q S G D L H K U N)
      rw [ComputablePolishSpaceTasteGate_single_carrier_alignment_decode P,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode E,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode R,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode A,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode Q,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode S,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode G,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode D,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode L,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode H,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode K,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode U,
        ComputablePolishSpaceTasteGate_single_carrier_alignment_decode N]

private theorem ComputablePolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ComputablePolishSpaceUp} :
    computablePolishSpaceToEventFlow x = computablePolishSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      computablePolishSpaceFromEventFlow (computablePolishSpaceToEventFlow x) =
        computablePolishSpaceFromEventFlow (computablePolishSpaceToEventFlow y) :=
    congrArg computablePolishSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ComputablePolishSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ComputablePolishSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance computablePolishSpaceBHistCarrier : BHistCarrier ComputablePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := computablePolishSpaceToEventFlow
  fromEventFlow := computablePolishSpaceFromEventFlow

instance computablePolishSpaceChapterTasteGate : ChapterTasteGate ComputablePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change computablePolishSpaceFromEventFlow (computablePolishSpaceToEventFlow x) = some x
    exact ComputablePolishSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ComputablePolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ComputablePolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  computablePolishSpaceChapterTasteGate

theorem ComputablePolishSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, computablePolishSpaceDecodeBHist (computablePolishSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ComputablePolishSpaceUp) ∧
        Nonempty (ChapterTasteGate ComputablePolishSpaceUp) ∧
          computablePolishSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ComputablePolishSpaceTasteGate_single_carrier_alignment_decode,
      ⟨computablePolishSpaceBHistCarrier⟩,
      ⟨computablePolishSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ComputablePolishSpaceUp
