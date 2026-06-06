import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICLocalDiamondWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICLocalDiamondWitnessUp : Type where
  | mk (K L R J B H C P N : BHist) : MetaCICLocalDiamondWitnessUp
  deriving DecidableEq

def metacicLocalDiamondWitnessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicLocalDiamondWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicLocalDiamondWitnessEncodeBHist h

def metacicLocalDiamondWitnessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicLocalDiamondWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicLocalDiamondWitnessDecodeBHist tail)

private theorem MetaCICLocalDiamondWitnessTasteGate_decode_encode :
    forall h : BHist,
      metacicLocalDiamondWitnessDecodeBHist
        (metacicLocalDiamondWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicLocalDiamondWitnessFields :
    MetaCICLocalDiamondWitnessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICLocalDiamondWitnessUp.mk K L R J B H C P N => [K, L, R, J, B, H, C, P, N]

def metacicLocalDiamondWitnessToEventFlow :
    MetaCICLocalDiamondWitnessUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (metacicLocalDiamondWitnessFields x).map metacicLocalDiamondWitnessEncodeBHist

def metacicLocalDiamondWitnessFromEventFlow :
    EventFlow -> Option MetaCICLocalDiamondWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | J :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (MetaCICLocalDiamondWitnessUp.mk
                                              (metacicLocalDiamondWitnessDecodeBHist K)
                                              (metacicLocalDiamondWitnessDecodeBHist L)
                                              (metacicLocalDiamondWitnessDecodeBHist R)
                                              (metacicLocalDiamondWitnessDecodeBHist J)
                                              (metacicLocalDiamondWitnessDecodeBHist B)
                                              (metacicLocalDiamondWitnessDecodeBHist H)
                                              (metacicLocalDiamondWitnessDecodeBHist C)
                                              (metacicLocalDiamondWitnessDecodeBHist P)
                                              (metacicLocalDiamondWitnessDecodeBHist N))
                                      | _ :: _ => none

private theorem metacicLocalDiamondWitness_round_trip :
    forall x : MetaCICLocalDiamondWitnessUp,
      metacicLocalDiamondWitnessFromEventFlow
        (metacicLocalDiamondWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K L R J B H C P N =>
      change
        some
          (MetaCICLocalDiamondWitnessUp.mk
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist K))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist L))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist R))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist J))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist B))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist H))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist C))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist P))
            (metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist N))) =
          some (MetaCICLocalDiamondWitnessUp.mk K L R J B H C P N)
      rw [MetaCICLocalDiamondWitnessTasteGate_decode_encode K,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode L,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode R,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode J,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode B,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode H,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode C,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode P,
        MetaCICLocalDiamondWitnessTasteGate_decode_encode N]

private theorem MetaCICLocalDiamondWitnessTasteGate_toEventFlow_injective
    {x y : MetaCICLocalDiamondWitnessUp} :
    metacicLocalDiamondWitnessToEventFlow x =
      metacicLocalDiamondWitnessToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicLocalDiamondWitnessFromEventFlow
          (metacicLocalDiamondWitnessToEventFlow x) =
        metacicLocalDiamondWitnessFromEventFlow
          (metacicLocalDiamondWitnessToEventFlow y) :=
    congrArg metacicLocalDiamondWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicLocalDiamondWitness_round_trip x).symm
      (Eq.trans hread (metacicLocalDiamondWitness_round_trip y)))

private theorem MetaCICLocalDiamondWitnessTasteGate_field_faithful :
    forall x y : MetaCICLocalDiamondWitnessUp,
      metacicLocalDiamondWitnessFields x =
        metacicLocalDiamondWitnessFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ L₁ R₁ J₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ L₂ R₂ J₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metacicLocalDiamondWitnessBHistCarrier :
    BHistCarrier MetaCICLocalDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicLocalDiamondWitnessToEventFlow
  fromEventFlow := metacicLocalDiamondWitnessFromEventFlow

instance metacicLocalDiamondWitnessChapterTasteGate :
    ChapterTasteGate MetaCICLocalDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicLocalDiamondWitnessFromEventFlow
        (metacicLocalDiamondWitnessToEventFlow x) = some x
    exact metacicLocalDiamondWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICLocalDiamondWitnessTasteGate_toEventFlow_injective heq)

instance metacicLocalDiamondWitnessFieldFaithful :
    FieldFaithful MetaCICLocalDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicLocalDiamondWitnessFields
  field_faithful := MetaCICLocalDiamondWitnessTasteGate_field_faithful

instance metacicLocalDiamondWitnessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICLocalDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICLocalDiamondWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICLocalDiamondWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICLocalDiamondWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicLocalDiamondWitnessChapterTasteGate

theorem MetaCICLocalDiamondWitnessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetaCICLocalDiamondWitnessUp) ∧
      Nonempty (FieldFaithful MetaCICLocalDiamondWitnessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetaCICLocalDiamondWitnessUp) ∧
          (∀ h : BHist,
            metacicLocalDiamondWitnessDecodeBHist
              (metacicLocalDiamondWitnessEncodeBHist h) = h) ∧
            metacicLocalDiamondWitnessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨metacicLocalDiamondWitnessChapterTasteGate⟩,
      ⟨metacicLocalDiamondWitnessFieldFaithful⟩,
      ⟨metacicLocalDiamondWitnessNontrivial⟩,
      MetaCICLocalDiamondWitnessTasteGate_decode_encode,
      rfl⟩

end BEDC.Derived.MetaCICLocalDiamondWitnessUp
