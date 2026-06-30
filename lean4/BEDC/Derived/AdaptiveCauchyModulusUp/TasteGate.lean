import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AdaptiveCauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AdaptiveCauchyModulusUp : Type where
  | mk (S D T W R E H C P N : BHist) : AdaptiveCauchyModulusUp
  deriving DecidableEq

def adaptiveCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: adaptiveCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: adaptiveCauchyModulusEncodeBHist h

def adaptiveCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (adaptiveCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (adaptiveCauchyModulusDecodeBHist tail)

private theorem AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, adaptiveCauchyModulusDecodeBHist
      (adaptiveCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def adaptiveCauchyModulusFields : AdaptiveCauchyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AdaptiveCauchyModulusUp.mk S D T W R E H C P N => [S, D, T, W, R, E, H, C, P, N]

def adaptiveCauchyModulusToEventFlow : AdaptiveCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (adaptiveCauchyModulusFields x).map adaptiveCauchyModulusEncodeBHist

def adaptiveCauchyModulusFromEventFlow : EventFlow → Option AdaptiveCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (AdaptiveCauchyModulusUp.mk
                                                  (adaptiveCauchyModulusDecodeBHist S)
                                                  (adaptiveCauchyModulusDecodeBHist D)
                                                  (adaptiveCauchyModulusDecodeBHist T)
                                                  (adaptiveCauchyModulusDecodeBHist W)
                                                  (adaptiveCauchyModulusDecodeBHist R)
                                                  (adaptiveCauchyModulusDecodeBHist E)
                                                  (adaptiveCauchyModulusDecodeBHist H)
                                                  (adaptiveCauchyModulusDecodeBHist C)
                                                  (adaptiveCauchyModulusDecodeBHist P)
                                                  (adaptiveCauchyModulusDecodeBHist N))
                                          | _ :: _ => none

private theorem AdaptiveCauchyModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AdaptiveCauchyModulusUp,
      adaptiveCauchyModulusFromEventFlow (adaptiveCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D T W R E H C P N =>
      change
        some
          (AdaptiveCauchyModulusUp.mk
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist S))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist D))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist T))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist W))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist R))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist E))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist H))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist C))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist P))
            (adaptiveCauchyModulusDecodeBHist (adaptiveCauchyModulusEncodeBHist N))) =
          some (AdaptiveCauchyModulusUp.mk S D T W R E H C P N)
      rw [AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode S,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode D,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode T,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode W,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode R,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode E,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode H,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode C,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode P,
        AdaptiveCauchyModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem AdaptiveCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AdaptiveCauchyModulusUp} :
    adaptiveCauchyModulusToEventFlow x = adaptiveCauchyModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      adaptiveCauchyModulusFromEventFlow (adaptiveCauchyModulusToEventFlow x) =
        adaptiveCauchyModulusFromEventFlow (adaptiveCauchyModulusToEventFlow y) :=
    congrArg adaptiveCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AdaptiveCauchyModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AdaptiveCauchyModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem AdaptiveCauchyModulusTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AdaptiveCauchyModulusUp,
      adaptiveCauchyModulusFields x = adaptiveCauchyModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 D1 T1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 D2 T2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance adaptiveCauchyModulusBHistCarrier : BHistCarrier AdaptiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := adaptiveCauchyModulusToEventFlow
  fromEventFlow := adaptiveCauchyModulusFromEventFlow

instance adaptiveCauchyModulusChapterTasteGate :
    ChapterTasteGate AdaptiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change adaptiveCauchyModulusFromEventFlow (adaptiveCauchyModulusToEventFlow x) = some x
    exact AdaptiveCauchyModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AdaptiveCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance adaptiveCauchyModulusFieldFaithful :
    FieldFaithful AdaptiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := adaptiveCauchyModulusFields
  field_faithful := AdaptiveCauchyModulusTasteGate_single_carrier_alignment_fields_faithful

instance adaptiveCauchyModulusNontrivial : Nontrivial AdaptiveCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AdaptiveCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AdaptiveCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AdaptiveCauchyModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AdaptiveCauchyModulusUp) ∧
      Nonempty (FieldFaithful AdaptiveCauchyModulusUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AdaptiveCauchyModulusUp) ∧
        adaptiveCauchyModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨adaptiveCauchyModulusChapterTasteGate⟩, ⟨adaptiveCauchyModulusFieldFaithful⟩,
      ⟨adaptiveCauchyModulusNontrivial⟩, rfl⟩

end BEDC.Derived.AdaptiveCauchyModulusUp
