import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialRealCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialRealCompactnessUp : Type where
  | mk : (S B I E Q R H C P N : BHist) → SequentialRealCompactnessUp
  deriving DecidableEq

def sequentialRealCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialRealCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialRealCompactnessEncodeBHist h

def sequentialRealCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialRealCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialRealCompactnessDecodeBHist tail)

private theorem SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialRealCompactnessToEventFlow : SequentialRealCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialRealCompactnessUp.mk S B I E Q R H C P N =>
      [sequentialRealCompactnessEncodeBHist S,
        sequentialRealCompactnessEncodeBHist B,
        sequentialRealCompactnessEncodeBHist I,
        sequentialRealCompactnessEncodeBHist E,
        sequentialRealCompactnessEncodeBHist Q,
        sequentialRealCompactnessEncodeBHist R,
        sequentialRealCompactnessEncodeBHist H,
        sequentialRealCompactnessEncodeBHist C,
        sequentialRealCompactnessEncodeBHist P,
        sequentialRealCompactnessEncodeBHist N]

def sequentialRealCompactnessFromEventFlow : EventFlow → Option SequentialRealCompactnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restB =>
      match restB with
      | [] => none
      | B :: restI =>
          match restI with
          | [] => none
          | I :: restE =>
              match restE with
              | [] => none
              | E :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restR =>
                      match restR with
                      | [] => none
                      | R :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (SequentialRealCompactnessUp.mk
                                                  (sequentialRealCompactnessDecodeBHist S)
                                                  (sequentialRealCompactnessDecodeBHist B)
                                                  (sequentialRealCompactnessDecodeBHist I)
                                                  (sequentialRealCompactnessDecodeBHist E)
                                                  (sequentialRealCompactnessDecodeBHist Q)
                                                  (sequentialRealCompactnessDecodeBHist R)
                                                  (sequentialRealCompactnessDecodeBHist H)
                                                  (sequentialRealCompactnessDecodeBHist C)
                                                  (sequentialRealCompactnessDecodeBHist P)
                                                  (sequentialRealCompactnessDecodeBHist N))
                                          | _ :: _ => none

def sequentialRealCompactnessFields : SequentialRealCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialRealCompactnessUp.mk S B I E Q R H C P N => [S, B, I, E, Q, R, H, C, P, N]

private theorem SequentialRealCompactnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SequentialRealCompactnessUp,
      sequentialRealCompactnessFromEventFlow (sequentialRealCompactnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B I E Q R H C P N =>
      change
        some
          (SequentialRealCompactnessUp.mk
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist S))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist B))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist I))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist E))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist Q))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist R))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist H))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist C))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist P))
            (sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist N))) =
          some (SequentialRealCompactnessUp.mk S B I E Q R H C P N)
      rw [SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode S,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode B,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode I,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode E,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode Q,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode R,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode H,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode C,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode P,
        SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem SequentialRealCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialRealCompactnessUp} :
    sequentialRealCompactnessToEventFlow x = sequentialRealCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialRealCompactnessFromEventFlow (sequentialRealCompactnessToEventFlow x) =
        sequentialRealCompactnessFromEventFlow (sequentialRealCompactnessToEventFlow y) :=
    congrArg sequentialRealCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SequentialRealCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentialRealCompactnessTasteGate_single_carrier_alignment_round_trip y)))

instance sequentialRealCompactnessBHistCarrier : BHistCarrier SequentialRealCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialRealCompactnessToEventFlow
  fromEventFlow := sequentialRealCompactnessFromEventFlow

instance sequentialRealCompactnessChapterTasteGate :
    ChapterTasteGate SequentialRealCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentialRealCompactnessFromEventFlow (sequentialRealCompactnessToEventFlow x) =
        some x
    exact SequentialRealCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentialRealCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sequentialRealCompactnessFieldFaithful :
    FieldFaithful SequentialRealCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentialRealCompactnessFields
  field_faithful := by
    intro x y h
    cases x with
    | mk S₁ B₁ I₁ E₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk S₂ B₂ I₂ E₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
            cases h
            rfl

instance sequentialRealCompactnessNontrivial :
    Nontrivial SequentialRealCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SequentialRealCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SequentialRealCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SequentialRealCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentialRealCompactnessDecodeBHist (sequentialRealCompactnessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SequentialRealCompactnessUp) ∧
        Nonempty (ChapterTasteGate SequentialRealCompactnessUp) ∧
          sequentialRealCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SequentialRealCompactnessTasteGate_single_carrier_alignment_decode_encode,
      ⟨sequentialRealCompactnessBHistCarrier⟩,
      ⟨sequentialRealCompactnessChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SequentialRealCompactnessUp
