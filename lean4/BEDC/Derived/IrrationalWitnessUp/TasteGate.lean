import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IrrationalWitnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IrrationalWitnessUp : Type where
  | mk (Q D S O T E H C P N : BHist) : IrrationalWitnessUp
  deriving DecidableEq

def irrationalWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: irrationalWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: irrationalWitnessEncodeBHist h

def irrationalWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (irrationalWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (irrationalWitnessDecodeBHist tail)

private theorem IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def irrationalWitnessFields : IrrationalWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IrrationalWitnessUp.mk Q D S O T E H C P N => [Q, D, S, O, T, E, H, C, P, N]

def irrationalWitnessToEventFlow : IrrationalWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (irrationalWitnessFields x).map irrationalWitnessEncodeBHist

private def IrrationalWitnessTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      IrrationalWitnessTasteGate_single_carrier_alignment_eventAt index rest

def irrationalWitnessFromEventFlow (ef : EventFlow) : Option IrrationalWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IrrationalWitnessUp.mk
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 0 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 1 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 2 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 3 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 4 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 5 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 6 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 7 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 8 ef))
      (irrationalWitnessDecodeBHist
        (IrrationalWitnessTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem IrrationalWitnessTasteGate_single_carrier_alignment_round_trip
    (x : IrrationalWitnessUp) :
    irrationalWitnessFromEventFlow (irrationalWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q D S O T E H C P N =>
      change
        some
          (IrrationalWitnessUp.mk
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist Q))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist D))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist S))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist O))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist T))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist E))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist H))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist C))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist P))
            (irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist N))) =
          some (IrrationalWitnessUp.mk Q D S O T E H C P N)
      rw [IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode Q,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode D,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode S,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode O,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode T,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode E,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode H,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode C,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode P,
        IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem IrrationalWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IrrationalWitnessUp} :
    irrationalWitnessToEventFlow x = irrationalWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      irrationalWitnessFromEventFlow (irrationalWitnessToEventFlow x) =
        irrationalWitnessFromEventFlow (irrationalWitnessToEventFlow y) :=
    congrArg irrationalWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IrrationalWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IrrationalWitnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem IrrationalWitnessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : IrrationalWitnessUp, irrationalWitnessFields x = irrationalWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ D₁ S₁ O₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ D₂ S₂ O₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance irrationalWitnessBHistCarrier : BHistCarrier IrrationalWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := irrationalWitnessToEventFlow
  fromEventFlow := irrationalWitnessFromEventFlow

instance irrationalWitnessChapterTasteGate : ChapterTasteGate IrrationalWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change irrationalWitnessFromEventFlow (irrationalWitnessToEventFlow x) = some x
    exact IrrationalWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IrrationalWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance irrationalWitnessFieldFaithful : FieldFaithful IrrationalWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := irrationalWitnessFields
  field_faithful := IrrationalWitnessTasteGate_single_carrier_alignment_fields_faithful

instance irrationalWitnessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial IrrationalWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IrrationalWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IrrationalWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def irrationalWitnessTasteGate : ChapterTasteGate IrrationalWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  irrationalWitnessChapterTasteGate

theorem IrrationalWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, irrationalWitnessDecodeBHist (irrationalWitnessEncodeBHist h) = h) ∧
      (∀ x : IrrationalWitnessUp,
        irrationalWitnessFromEventFlow (irrationalWitnessToEventFlow x) = some x) ∧
        (∀ x y : IrrationalWitnessUp,
          irrationalWitnessToEventFlow x = irrationalWitnessToEventFlow y → x = y) ∧
          irrationalWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨IrrationalWitnessTasteGate_single_carrier_alignment_decode_encode,
      IrrationalWitnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => IrrationalWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.IrrationalWitnessUp.TasteGate
