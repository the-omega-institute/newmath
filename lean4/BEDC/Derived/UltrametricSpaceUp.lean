import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UltrametricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UltrametricSpaceUp : Type where
  | mk
      (metricRow radiusRow triangleRow ballRow exampleRow transportRow replayRow provenanceRow
        localCert : BHist) :
      UltrametricSpaceUp
  deriving DecidableEq

def ultrametricSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ultrametricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ultrametricSpaceEncodeBHist h

def ultrametricSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ultrametricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ultrametricSpaceDecodeBHist tail)

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_decode :
    forall h : BHist, ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ultrametricSpaceFields : UltrametricSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UltrametricSpaceUp.mk M V T B E H K P N => [M, V, T, B, E, H, K, P, N]

def ultrametricSpaceToEventFlow : UltrametricSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ultrametricSpaceFields x).map ultrametricSpaceEncodeBHist

private def ultrametricSpaceRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => ultrametricSpaceRawAt n rest

def ultrametricSpaceFromEventFlow (flow : EventFlow) : Option UltrametricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UltrametricSpaceUp.mk
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 0 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 1 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 2 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 3 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 4 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 5 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 6 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 7 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 8 flow)))

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_round_trip
    (x : UltrametricSpaceUp) :
    ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M V T B E H K P N =>
      change
        some
          (UltrametricSpaceUp.mk
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist M))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist V))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist T))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist B))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist E))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist H))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist K))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist P))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist N))) =
          some (UltrametricSpaceUp.mk M V T B E H K P N)
      rw [UltrametricSpaceTasteGate_single_carrier_alignment_decode M,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode V,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode T,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode B,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode E,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode H,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode K,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode P,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode N]

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UltrametricSpaceUp} :
    ultrametricSpaceToEventFlow x = ultrametricSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) =
        ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow y) :=
    congrArg ultrametricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UltrametricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UltrametricSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : UltrametricSpaceUp,
      ultrametricSpaceFields x = ultrametricSpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Ma Va Ta Ba Ea Ha Ka Pa Na =>
      cases y with
      | mk Mb Vb Tb Bb Eb Hb Kb Pb Nb =>
          cases hfields
          rfl

instance ultrametricSpaceBHistCarrier : BHistCarrier UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ultrametricSpaceToEventFlow
  fromEventFlow := ultrametricSpaceFromEventFlow

instance ultrametricSpaceChapterTasteGate : ChapterTasteGate UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) = some x
    exact UltrametricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UltrametricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ultrametricSpaceFieldFaithful : FieldFaithful UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ultrametricSpaceFields
  field_faithful := UltrametricSpaceTasteGate_single_carrier_alignment_fields_faithful

instance ultrametricSpaceNontrivial : Nontrivial UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UltrametricSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UltrametricSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem UltrametricSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UltrametricSpaceUp) ∧
      Nonempty (FieldFaithful UltrametricSpaceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial UltrametricSpaceUp) ∧
      (∀ h : BHist, ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist h) = h) ∧
      (∀ x : UltrametricSpaceUp,
        ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) = some x) ∧
      (∀ x y : UltrametricSpaceUp,
        ultrametricSpaceToEventFlow x = ultrametricSpaceToEventFlow y -> x = y) ∧
      ultrametricSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨ultrametricSpaceChapterTasteGate⟩, ⟨ultrametricSpaceFieldFaithful⟩,
      ⟨ultrametricSpaceNontrivial⟩,
      UltrametricSpaceTasteGate_single_carrier_alignment_decode,
      UltrametricSpaceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => UltrametricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.UltrametricSpaceUp
