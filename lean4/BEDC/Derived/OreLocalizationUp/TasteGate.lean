import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OreLocalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OreLocalizationUp : Type where
  | mk (R S O C F D H T P N : BHist) : OreLocalizationUp
  deriving DecidableEq

def oreLocalizationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oreLocalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oreLocalizationEncodeBHist h

def oreLocalizationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oreLocalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oreLocalizationDecodeBHist tail)

private theorem OreLocalizationTasteGate_single_carrier_alignment_decode :
    forall h : BHist, oreLocalizationDecodeBHist (oreLocalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oreLocalizationFields : OreLocalizationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OreLocalizationUp.mk R S O C F D H T P N => [R, S, O, C, F, D, H, T, P, N]

def oreLocalizationToEventFlow : OreLocalizationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (oreLocalizationFields x).map oreLocalizationEncodeBHist

private def oreLocalizationEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, event :: _ => event
  | Nat.succ n, _ :: rest => oreLocalizationEventAt n rest
  | _, [] => []

def oreLocalizationFromEventFlow (flow : EventFlow) : Option OreLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OreLocalizationUp.mk
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 0 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 1 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 2 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 3 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 4 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 5 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 6 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 7 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 8 flow))
      (oreLocalizationDecodeBHist (oreLocalizationEventAt 9 flow)))

private theorem OreLocalizationTasteGate_single_carrier_alignment_round_trip :
    forall x : OreLocalizationUp,
      oreLocalizationFromEventFlow (oreLocalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S O C F D H T P N =>
      change
        some
          (OreLocalizationUp.mk
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist R))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist S))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist O))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist C))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist F))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist D))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist H))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist T))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist P))
            (oreLocalizationDecodeBHist (oreLocalizationEncodeBHist N))) =
          some (OreLocalizationUp.mk R S O C F D H T P N)
      rw [OreLocalizationTasteGate_single_carrier_alignment_decode R,
        OreLocalizationTasteGate_single_carrier_alignment_decode S,
        OreLocalizationTasteGate_single_carrier_alignment_decode O,
        OreLocalizationTasteGate_single_carrier_alignment_decode C,
        OreLocalizationTasteGate_single_carrier_alignment_decode F,
        OreLocalizationTasteGate_single_carrier_alignment_decode D,
        OreLocalizationTasteGate_single_carrier_alignment_decode H,
        OreLocalizationTasteGate_single_carrier_alignment_decode T,
        OreLocalizationTasteGate_single_carrier_alignment_decode P,
        OreLocalizationTasteGate_single_carrier_alignment_decode N]

private theorem OreLocalizationTasteGate_single_carrier_alignment_injective
    {x y : OreLocalizationUp} :
    oreLocalizationToEventFlow x = oreLocalizationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oreLocalizationFromEventFlow (oreLocalizationToEventFlow x) =
        oreLocalizationFromEventFlow (oreLocalizationToEventFlow y) :=
    congrArg oreLocalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OreLocalizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OreLocalizationTasteGate_single_carrier_alignment_round_trip y)))

private theorem OreLocalizationTasteGate_single_carrier_alignment_fields :
    forall x y : OreLocalizationUp, oreLocalizationFields x = oreLocalizationFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 S1 O1 C1 F1 D1 H1 T1 P1 N1 =>
      cases y with
      | mk R2 S2 O2 C2 F2 D2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance oreLocalizationBHistCarrier : BHistCarrier OreLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oreLocalizationToEventFlow
  fromEventFlow := oreLocalizationFromEventFlow

instance oreLocalizationChapterTasteGate : ChapterTasteGate OreLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change oreLocalizationFromEventFlow (oreLocalizationToEventFlow x) = some x
    exact OreLocalizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OreLocalizationTasteGate_single_carrier_alignment_injective heq)

instance oreLocalizationFieldFaithful : FieldFaithful OreLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := oreLocalizationFields
  field_faithful := OreLocalizationTasteGate_single_carrier_alignment_fields

instance oreLocalizationNontrivial : Nontrivial OreLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OreLocalizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OreLocalizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OreLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  oreLocalizationChapterTasteGate

theorem OreLocalizationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate OreLocalizationUp) /\
      Nonempty (FieldFaithful OreLocalizationUp) /\
        Nonempty (Nontrivial OreLocalizationUp) /\
          (forall h : BHist, oreLocalizationDecodeBHist (oreLocalizationEncodeBHist h) = h) /\
            (forall x : OreLocalizationUp,
              oreLocalizationFromEventFlow (oreLocalizationToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨oreLocalizationChapterTasteGate⟩,
      ⟨oreLocalizationFieldFaithful⟩,
      ⟨oreLocalizationNontrivial⟩,
      OreLocalizationTasteGate_single_carrier_alignment_decode,
      OreLocalizationTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.OreLocalizationUp
