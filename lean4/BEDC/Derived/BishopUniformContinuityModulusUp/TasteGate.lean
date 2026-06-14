import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopUniformContinuityModulusUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopUniformContinuityModulusUp : Type where
  | mk (S F T L D R E H C P N : BHist) : BishopUniformContinuityModulusUp
  deriving DecidableEq

def bishopUniformContinuityModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopUniformContinuityModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopUniformContinuityModulusEncodeBHist h

def bishopUniformContinuityModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopUniformContinuityModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopUniformContinuityModulusDecodeBHist tail)

private theorem BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopUniformContinuityModulusDecodeBHist
        (bishopUniformContinuityModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopUniformContinuityModulusFields :
    BishopUniformContinuityModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopUniformContinuityModulusUp.mk S F T L D R E H C P N =>
      [S, F, T, L, D, R, E, H, C, P, N]

def bishopUniformContinuityModulusToEventFlow :
    BishopUniformContinuityModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopUniformContinuityModulusFields x).map
        bishopUniformContinuityModulusEncodeBHist

def bishopUniformContinuityModulusFromEventFlow :
    EventFlow → Option BishopUniformContinuityModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | F :: restF =>
          match restF with
          | T :: restT =>
              match restT with
              | L :: restL =>
                  match restL with
                  | D :: restD =>
                      match restD with
                      | R :: restR =>
                          match restR with
                          | E :: restE =>
                              match restE with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (BishopUniformContinuityModulusUp.mk
                                                      (bishopUniformContinuityModulusDecodeBHist S)
                                                      (bishopUniformContinuityModulusDecodeBHist F)
                                                      (bishopUniformContinuityModulusDecodeBHist T)
                                                      (bishopUniformContinuityModulusDecodeBHist L)
                                                      (bishopUniformContinuityModulusDecodeBHist D)
                                                      (bishopUniformContinuityModulusDecodeBHist R)
                                                      (bishopUniformContinuityModulusDecodeBHist E)
                                                      (bishopUniformContinuityModulusDecodeBHist H)
                                                      (bishopUniformContinuityModulusDecodeBHist C)
                                                      (bishopUniformContinuityModulusDecodeBHist P)
                                                      (bishopUniformContinuityModulusDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem BishopUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopUniformContinuityModulusUp,
      bishopUniformContinuityModulusFromEventFlow
        (bishopUniformContinuityModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F T L D R E H C P N =>
      change
        some
            (BishopUniformContinuityModulusUp.mk
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist S))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist F))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist T))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist L))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist D))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist R))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist E))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist H))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist C))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist P))
              (bishopUniformContinuityModulusDecodeBHist
                (bishopUniformContinuityModulusEncodeBHist N))) =
          some (BishopUniformContinuityModulusUp.mk S F T L D R E H C P N)
      rw [BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode S,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode F,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode T,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode L,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode D,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode R,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode E,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode H,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode C,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode P,
        BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode N]

private theorem bishopUniformContinuityModulusToEventFlow_injective
    {x y : BishopUniformContinuityModulusUp} :
    bishopUniformContinuityModulusToEventFlow x =
        bishopUniformContinuityModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopUniformContinuityModulusFromEventFlow
          (bishopUniformContinuityModulusToEventFlow x) =
        bishopUniformContinuityModulusFromEventFlow
          (bishopUniformContinuityModulusToEventFlow y) :=
    congrArg bishopUniformContinuityModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem bishopUniformContinuityModulus_field_faithful :
    ∀ x y : BishopUniformContinuityModulusUp,
      bishopUniformContinuityModulusFields x =
          bishopUniformContinuityModulusFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S F T L D R E H C P N =>
      cases y with
      | mk S' F' T' L' D' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance bishopUniformContinuityModulusBHistCarrier :
    BHistCarrier BishopUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopUniformContinuityModulusToEventFlow
  fromEventFlow := bishopUniformContinuityModulusFromEventFlow

instance bishopUniformContinuityModulusChapterTasteGate :
    ChapterTasteGate BishopUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopUniformContinuityModulusFromEventFlow
        (bishopUniformContinuityModulusToEventFlow x) = some x
    exact BishopUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopUniformContinuityModulusToEventFlow_injective heq)

instance bishopUniformContinuityModulusFieldFaithful :
    FieldFaithful BishopUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopUniformContinuityModulusFields
  field_faithful := bishopUniformContinuityModulus_field_faithful

instance bishopUniformContinuityModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopUniformContinuityModulusUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BishopUniformContinuityModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopUniformContinuityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopUniformContinuityModulusChapterTasteGate

theorem BishopUniformContinuityModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopUniformContinuityModulusUp) ∧
      Nonempty (FieldFaithful BishopUniformContinuityModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopUniformContinuityModulusUp) ∧
      (∀ h : BHist,
        bishopUniformContinuityModulusDecodeBHist
          (bishopUniformContinuityModulusEncodeBHist h) = h) ∧
      (∀ x : BishopUniformContinuityModulusUp,
        bishopUniformContinuityModulusFromEventFlow
          (bishopUniformContinuityModulusToEventFlow x) = some x) ∧
      bishopUniformContinuityModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨bishopUniformContinuityModulusChapterTasteGate⟩
  constructor
  · exact ⟨bishopUniformContinuityModulusFieldFaithful⟩
  constructor
  · exact ⟨bishopUniformContinuityModulusNontrivial⟩
  constructor
  · exact BishopUniformContinuityModulusTasteGate_single_carrier_alignment_decode
  constructor
  · exact BishopUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip
  · rfl

end TasteGate
end BEDC.Derived.BishopUniformContinuityModulusUp
