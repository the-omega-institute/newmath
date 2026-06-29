import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletenessWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletenessWitnessUp : Type where
  | mk (S D R E H C P N : BHist) : RealCompletenessWitnessUp
  deriving DecidableEq

def realCompletenessWitnessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletenessWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletenessWitnessEncodeBHist h

def realCompletenessWitnessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletenessWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletenessWitnessDecodeBHist tail)

private theorem realCompletenessWitness_decode_encode_bhist :
    forall h : BHist,
      realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCompletenessWitnessFields : RealCompletenessWitnessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletenessWitnessUp.mk S D R E H C P N =>
      [S, D, R, E, H, C, P, N]

def realCompletenessWitnessToEventFlow : RealCompletenessWitnessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletenessWitnessUp.mk S D R E H C P N =>
      [realCompletenessWitnessEncodeBHist S,
        realCompletenessWitnessEncodeBHist D,
        realCompletenessWitnessEncodeBHist R,
        realCompletenessWitnessEncodeBHist E,
        realCompletenessWitnessEncodeBHist H,
        realCompletenessWitnessEncodeBHist C,
        realCompletenessWitnessEncodeBHist P,
        realCompletenessWitnessEncodeBHist N]

def realCompletenessWitnessFromEventFlow :
    EventFlow -> Option RealCompletenessWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, D, R, E, H, C, P, N] =>
      some
        (RealCompletenessWitnessUp.mk
          (realCompletenessWitnessDecodeBHist S)
          (realCompletenessWitnessDecodeBHist D)
          (realCompletenessWitnessDecodeBHist R)
          (realCompletenessWitnessDecodeBHist E)
          (realCompletenessWitnessDecodeBHist H)
          (realCompletenessWitnessDecodeBHist C)
          (realCompletenessWitnessDecodeBHist P)
          (realCompletenessWitnessDecodeBHist N))
  | _ => none

private theorem realCompletenessWitness_round_trip :
    forall x : RealCompletenessWitnessUp,
      realCompletenessWitnessFromEventFlow (realCompletenessWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D R E H C P N =>
      change
        some
          (RealCompletenessWitnessUp.mk
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist S))
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist D))
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist R))
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist E))
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist H))
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist C))
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist P))
            (realCompletenessWitnessDecodeBHist (realCompletenessWitnessEncodeBHist N))) =
          some (RealCompletenessWitnessUp.mk S D R E H C P N)
      rw [realCompletenessWitness_decode_encode_bhist S,
        realCompletenessWitness_decode_encode_bhist D,
        realCompletenessWitness_decode_encode_bhist R,
        realCompletenessWitness_decode_encode_bhist E,
        realCompletenessWitness_decode_encode_bhist H,
        realCompletenessWitness_decode_encode_bhist C,
        realCompletenessWitness_decode_encode_bhist P,
        realCompletenessWitness_decode_encode_bhist N]

private theorem realCompletenessWitnessToEventFlow_injective
    {x y : RealCompletenessWitnessUp} :
    realCompletenessWitnessToEventFlow x = realCompletenessWitnessToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletenessWitnessFromEventFlow (realCompletenessWitnessToEventFlow x) =
        realCompletenessWitnessFromEventFlow (realCompletenessWitnessToEventFlow y) :=
    congrArg realCompletenessWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletenessWitness_round_trip x).symm
      (Eq.trans hread (realCompletenessWitness_round_trip y)))

private theorem realCompletenessWitness_field_faithful :
    forall x y : RealCompletenessWitnessUp,
      realCompletenessWitnessFields x = realCompletenessWitnessFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 D2 R2 E2 H2 C2 P2 N2 =>
          cases h
          rfl

instance realCompletenessWitnessBHistCarrier :
    BHistCarrier RealCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletenessWitnessToEventFlow
  fromEventFlow := realCompletenessWitnessFromEventFlow

instance realCompletenessWitnessChapterTasteGate :
    ChapterTasteGate RealCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletenessWitnessFromEventFlow (realCompletenessWitnessToEventFlow x) =
      some x
    exact realCompletenessWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletenessWitnessToEventFlow_injective heq)

instance realCompletenessWitnessFieldFaithful :
    FieldFaithful RealCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCompletenessWitnessFields
  field_faithful := realCompletenessWitness_field_faithful

instance realCompletenessWitnessNontrivial :
    Nontrivial RealCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletenessWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletenessWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCompletenessWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletenessWitnessChapterTasteGate

theorem RealCompletenessWitnessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealCompletenessWitnessUp) ∧
      Nonempty (FieldFaithful RealCompletenessWitnessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealCompletenessWitnessUp) ∧
          (∀ h : BHist,
            realCompletenessWitnessDecodeBHist
              (realCompletenessWitnessEncodeBHist h) = h) ∧
            (∀ x : RealCompletenessWitnessUp,
              realCompletenessWitnessFromEventFlow
                (realCompletenessWitnessToEventFlow x) = some x) ∧
              (∀ x y : RealCompletenessWitnessUp,
                realCompletenessWitnessToEventFlow x =
                  realCompletenessWitnessToEventFlow y -> x = y) ∧
                realCompletenessWitnessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨realCompletenessWitnessChapterTasteGate⟩,
      ⟨realCompletenessWitnessFieldFaithful⟩,
      ⟨realCompletenessWitnessNontrivial⟩,
      realCompletenessWitness_decode_encode_bhist,
      realCompletenessWitness_round_trip,
      by
        intro x y heq
        exact realCompletenessWitnessToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealCompletenessWitnessUp
