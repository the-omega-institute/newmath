import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChuSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChuSpaceUp : Type where
  | mk (S O E D T H C P N : BHist) : ChuSpaceUp
  deriving DecidableEq

def chuSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: chuSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: chuSpaceEncodeBHist h

def chuSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (chuSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (chuSpaceDecodeBHist tail)

private theorem ChuSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, chuSpaceDecodeBHist (chuSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def chuSpaceFields : ChuSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChuSpaceUp.mk S O E D T H C P N => [S, O, E, D, T, H, C, P, N]

def chuSpaceToEventFlow : ChuSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (chuSpaceFields x).map chuSpaceEncodeBHist

private def chuSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => chuSpaceEventAt index rest

def chuSpaceFromEventFlow (ef : EventFlow) : Option ChuSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ChuSpaceUp.mk
      (chuSpaceDecodeBHist (chuSpaceEventAt 0 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 1 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 2 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 3 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 4 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 5 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 6 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 7 ef))
      (chuSpaceDecodeBHist (chuSpaceEventAt 8 ef)))

private theorem ChuSpaceTasteGate_single_carrier_alignment_round_trip
    (x : ChuSpaceUp) :
    chuSpaceFromEventFlow (chuSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S O E D T H C P N =>
      change
        some
          (ChuSpaceUp.mk
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist S))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist O))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist E))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist D))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist T))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist H))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist C))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist P))
            (chuSpaceDecodeBHist (chuSpaceEncodeBHist N))) =
          some (ChuSpaceUp.mk S O E D T H C P N)
      rw [ChuSpaceTasteGate_single_carrier_alignment_decode S,
        ChuSpaceTasteGate_single_carrier_alignment_decode O,
        ChuSpaceTasteGate_single_carrier_alignment_decode E,
        ChuSpaceTasteGate_single_carrier_alignment_decode D,
        ChuSpaceTasteGate_single_carrier_alignment_decode T,
        ChuSpaceTasteGate_single_carrier_alignment_decode H,
        ChuSpaceTasteGate_single_carrier_alignment_decode C,
        ChuSpaceTasteGate_single_carrier_alignment_decode P,
        ChuSpaceTasteGate_single_carrier_alignment_decode N]

private theorem ChuSpaceTasteGate_single_carrier_alignment_injective
    {x y : ChuSpaceUp} :
    chuSpaceToEventFlow x = chuSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      chuSpaceFromEventFlow (chuSpaceToEventFlow x) =
        chuSpaceFromEventFlow (chuSpaceToEventFlow y) :=
    congrArg chuSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ChuSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ChuSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem ChuSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : ChuSpaceUp, chuSpaceFields x = chuSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ O₁ E₁ D₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ O₂ E₂ D₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance chuSpaceBHistCarrier : BHistCarrier ChuSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := chuSpaceToEventFlow
  fromEventFlow := chuSpaceFromEventFlow

instance chuSpaceChapterTasteGate : ChapterTasteGate ChuSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change chuSpaceFromEventFlow (chuSpaceToEventFlow x) = some x
    exact ChuSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ChuSpaceTasteGate_single_carrier_alignment_injective heq)

instance chuSpaceFieldFaithful : FieldFaithful ChuSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := chuSpaceFields
  field_faithful := ChuSpaceTasteGate_single_carrier_alignment_fields

instance chuSpaceNontrivial : BEDC.Meta.TasteGate.Nontrivial ChuSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChuSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ChuSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ChuSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, chuSpaceDecodeBHist (chuSpaceEncodeBHist h) = h) ∧
      (∀ x : ChuSpaceUp, chuSpaceFromEventFlow (chuSpaceToEventFlow x) = some x) ∧
        (∀ x y : ChuSpaceUp, chuSpaceToEventFlow x = chuSpaceToEventFlow y → x = y) ∧
          chuSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ChuSpaceTasteGate_single_carrier_alignment_decode
  constructor
  · exact ChuSpaceTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact ChuSpaceTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.ChuSpaceUp
