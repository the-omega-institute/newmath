import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteBracketingIntervalUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteBracketingIntervalUp : Type where
  | mk (L U D W R E S H C P N : BHist) : FiniteBracketingIntervalUp
  deriving DecidableEq

def finiteBracketingIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteBracketingIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteBracketingIntervalEncodeBHist h

def finiteBracketingIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteBracketingIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteBracketingIntervalDecodeBHist tail)

private theorem finiteBracketingIntervalDecode_encode_bhist :
    ∀ h : BHist,
      finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteBracketingIntervalFields : FiniteBracketingIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteBracketingIntervalUp.mk L U D W R E S H C P N => [L, U, D, W, R, E, S, H, C, P, N]

def finiteBracketingIntervalToEventFlow : FiniteBracketingIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteBracketingIntervalFields x).map finiteBracketingIntervalEncodeBHist

def finiteBracketingIntervalFromEventFlow : EventFlow → Option FiniteBracketingIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | L :: restU =>
      match restU with
      | U :: restD =>
          match restD with
          | D :: restW =>
              match restW with
              | W :: restR =>
                  match restR with
                  | R :: restE =>
                      match restE with
                      | E :: restS =>
                          match restS with
                          | S :: restH =>
                              match restH with
                              | H :: restC =>
                                  match restC with
                                  | C :: restP =>
                                      match restP with
                                      | P :: restN =>
                                          match restN with
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (FiniteBracketingIntervalUp.mk
                                                      (finiteBracketingIntervalDecodeBHist L)
                                                      (finiteBracketingIntervalDecodeBHist U)
                                                      (finiteBracketingIntervalDecodeBHist D)
                                                      (finiteBracketingIntervalDecodeBHist W)
                                                      (finiteBracketingIntervalDecodeBHist R)
                                                      (finiteBracketingIntervalDecodeBHist E)
                                                      (finiteBracketingIntervalDecodeBHist S)
                                                      (finiteBracketingIntervalDecodeBHist H)
                                                      (finiteBracketingIntervalDecodeBHist C)
                                                      (finiteBracketingIntervalDecodeBHist P)
                                                      (finiteBracketingIntervalDecodeBHist N))
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

private theorem finiteBracketingInterval_round_trip :
    ∀ x : FiniteBracketingIntervalUp,
      finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U D W R E S H C P N =>
      change
        some
            (FiniteBracketingIntervalUp.mk
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist L))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist U))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist D))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist W))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist R))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist E))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist S))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist H))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist C))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist P))
              (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist N))) =
          some (FiniteBracketingIntervalUp.mk L U D W R E S H C P N)
      rw [finiteBracketingIntervalDecode_encode_bhist L,
        finiteBracketingIntervalDecode_encode_bhist U,
        finiteBracketingIntervalDecode_encode_bhist D,
        finiteBracketingIntervalDecode_encode_bhist W,
        finiteBracketingIntervalDecode_encode_bhist R,
        finiteBracketingIntervalDecode_encode_bhist E,
        finiteBracketingIntervalDecode_encode_bhist S,
        finiteBracketingIntervalDecode_encode_bhist H,
        finiteBracketingIntervalDecode_encode_bhist C,
        finiteBracketingIntervalDecode_encode_bhist P,
        finiteBracketingIntervalDecode_encode_bhist N]

private theorem finiteBracketingIntervalToEventFlow_injective
    {x y : FiniteBracketingIntervalUp} :
    finiteBracketingIntervalToEventFlow x = finiteBracketingIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) =
        finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow y) :=
    congrArg finiteBracketingIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteBracketingInterval_round_trip x).symm
      (Eq.trans hread (finiteBracketingInterval_round_trip y)))

private theorem finiteBracketingInterval_fields_faithful :
    ∀ x y : FiniteBracketingIntervalUp,
      finiteBracketingIntervalFields x = finiteBracketingIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 D1 W1 R1 E1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 D2 W2 R2 E2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteBracketingIntervalBHistCarrier : BHistCarrier FiniteBracketingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteBracketingIntervalToEventFlow
  fromEventFlow := finiteBracketingIntervalFromEventFlow

instance finiteBracketingIntervalChapterTasteGate :
    ChapterTasteGate FiniteBracketingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) = some x
    exact finiteBracketingInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteBracketingIntervalToEventFlow_injective heq)

instance finiteBracketingIntervalFieldFaithful :
    FieldFaithful FiniteBracketingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteBracketingIntervalFields
  field_faithful := finiteBracketingInterval_fields_faithful

instance finiteBracketingIntervalNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteBracketingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteBracketingIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteBracketingIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteBracketingIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteBracketingIntervalChapterTasteGate

theorem FiniteBracketingIntervalTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteBracketingIntervalUp) ∧
      Nonempty (FieldFaithful FiniteBracketingIntervalUp) ∧
        Nonempty (Nontrivial FiniteBracketingIntervalUp) ∧
          (∀ h : BHist,
            finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist h) = h) ∧
            (∀ x : FiniteBracketingIntervalUp,
              finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) =
                some x) ∧
              (∀ x y : FiniteBracketingIntervalUp,
                finiteBracketingIntervalToEventFlow x = finiteBracketingIntervalToEventFlow y →
                  x = y) ∧
                finiteBracketingIntervalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨finiteBracketingIntervalChapterTasteGate⟩
  · constructor
    · exact ⟨finiteBracketingIntervalFieldFaithful⟩
    · constructor
      · exact ⟨finiteBracketingIntervalNontrivial⟩
      · constructor
        · exact finiteBracketingIntervalDecode_encode_bhist
        · constructor
          · exact finiteBracketingInterval_round_trip
          · constructor
            · intro x y heq
              exact finiteBracketingIntervalToEventFlow_injective heq
            · rfl

end TasteGate
end BEDC.Derived.FiniteBracketingIntervalUp
