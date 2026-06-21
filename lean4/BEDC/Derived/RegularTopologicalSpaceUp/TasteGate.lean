import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularTopologicalSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularTopologicalSpaceUp : Type where
  | mk (T O F M S H C P N : BHist) : RegularTopologicalSpaceUp
  deriving DecidableEq

def regularTopologicalSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularTopologicalSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularTopologicalSpaceEncodeBHist h

def regularTopologicalSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularTopologicalSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularTopologicalSpaceDecodeBHist tail)

private theorem RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularTopologicalSpaceFields : RegularTopologicalSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularTopologicalSpaceUp.mk T O F M S H C P N => [T, O, F, M, S, H, C, P, N]

def regularTopologicalSpaceToEventFlow : RegularTopologicalSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularTopologicalSpaceFields x).map regularTopologicalSpaceEncodeBHist

private def regularTopologicalSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularTopologicalSpaceEventAtDefault index rest

def regularTopologicalSpaceFromEventFlow (ef : EventFlow) :
    Option RegularTopologicalSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularTopologicalSpaceUp.mk
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 0 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 1 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 2 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 3 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 4 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 5 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 6 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 7 ef))
      (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEventAtDefault 8 ef)))

private theorem RegularTopologicalSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularTopologicalSpaceUp,
      regularTopologicalSpaceFromEventFlow (regularTopologicalSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk T O F M S H C P N =>
      change
        some
          (RegularTopologicalSpaceUp.mk
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist T))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist O))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist F))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist M))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist S))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist H))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist C))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist P))
            (regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist N))) =
          some (RegularTopologicalSpaceUp.mk T O F M S H C P N)
      rw [RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode T,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode O,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode F,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode M,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode S,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode H,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode C,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode P,
        RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode N]

private theorem RegularTopologicalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularTopologicalSpaceUp} :
    regularTopologicalSpaceToEventFlow x = regularTopologicalSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularTopologicalSpaceFromEventFlow (regularTopologicalSpaceToEventFlow x) =
        regularTopologicalSpaceFromEventFlow (regularTopologicalSpaceToEventFlow y) :=
    congrArg regularTopologicalSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularTopologicalSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularTopologicalSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance regularTopologicalSpaceBHistCarrier : BHistCarrier RegularTopologicalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularTopologicalSpaceToEventFlow
  fromEventFlow := regularTopologicalSpaceFromEventFlow

instance regularTopologicalSpaceChapterTasteGate :
    ChapterTasteGate RegularTopologicalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularTopologicalSpaceFromEventFlow (regularTopologicalSpaceToEventFlow x) =
      some x
    exact RegularTopologicalSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularTopologicalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularTopologicalSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularTopologicalSpaceDecodeBHist (regularTopologicalSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularTopologicalSpaceUp) ∧
        Nonempty (ChapterTasteGate RegularTopologicalSpaceUp) ∧
          regularTopologicalSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularTopologicalSpaceTasteGate_single_carrier_alignment_decode,
      ⟨regularTopologicalSpaceBHistCarrier⟩, ⟨regularTopologicalSpaceChapterTasteGate⟩, rfl⟩

end BEDC.Derived.RegularTopologicalSpaceUp
