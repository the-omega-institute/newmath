import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineBorelFiniteSubcoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineBorelFiniteSubcoverUp : Type where
  | mk (I D W R S T C P N : BHist) : HeineBorelFiniteSubcoverUp
  deriving DecidableEq

def heineBorelFiniteSubcoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineBorelFiniteSubcoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineBorelFiniteSubcoverEncodeBHist h

def heineBorelFiniteSubcoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineBorelFiniteSubcoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineBorelFiniteSubcoverDecodeBHist tail)

private theorem HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heineBorelFiniteSubcoverFields : HeineBorelFiniteSubcoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeineBorelFiniteSubcoverUp.mk I D W R S T C P N => [I, D, W, R, S, T, C, P, N]

def heineBorelFiniteSubcoverToEventFlow : HeineBorelFiniteSubcoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (heineBorelFiniteSubcoverFields x).map heineBorelFiniteSubcoverEncodeBHist

def heineBorelFiniteSubcoverFromEventFlow :
    EventFlow → Option HeineBorelFiniteSubcoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
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
                                            (HeineBorelFiniteSubcoverUp.mk
                                              (heineBorelFiniteSubcoverDecodeBHist I)
                                              (heineBorelFiniteSubcoverDecodeBHist D)
                                              (heineBorelFiniteSubcoverDecodeBHist W)
                                              (heineBorelFiniteSubcoverDecodeBHist R)
                                              (heineBorelFiniteSubcoverDecodeBHist S)
                                              (heineBorelFiniteSubcoverDecodeBHist T)
                                              (heineBorelFiniteSubcoverDecodeBHist C)
                                              (heineBorelFiniteSubcoverDecodeBHist P)
                                              (heineBorelFiniteSubcoverDecodeBHist N))
                                      | _ :: _ => none

private theorem HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_round_trip
    (x : HeineBorelFiniteSubcoverUp) :
    heineBorelFiniteSubcoverFromEventFlow (heineBorelFiniteSubcoverToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I D W R S T C P N =>
      change
        some
          (HeineBorelFiniteSubcoverUp.mk
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist I))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist D))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist W))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist R))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist S))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist T))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist C))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist P))
            (heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist N))) =
          some (HeineBorelFiniteSubcoverUp.mk I D W R S T C P N)
      rw [HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode I,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode D,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode W,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode R,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode S,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode T,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode C,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode P,
        HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_injective
    {x y : HeineBorelFiniteSubcoverUp} :
    heineBorelFiniteSubcoverToEventFlow x = heineBorelFiniteSubcoverToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineBorelFiniteSubcoverFromEventFlow (heineBorelFiniteSubcoverToEventFlow x) =
        heineBorelFiniteSubcoverFromEventFlow (heineBorelFiniteSubcoverToEventFlow y) :=
    congrArg heineBorelFiniteSubcoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_round_trip y)))

private theorem HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_fields :
    ∀ x y : HeineBorelFiniteSubcoverUp,
      heineBorelFiniteSubcoverFields x = heineBorelFiniteSubcoverFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ D₁ W₁ R₁ S₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ D₂ W₂ R₂ S₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance heineBorelFiniteSubcoverBHistCarrier :
    BHistCarrier HeineBorelFiniteSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineBorelFiniteSubcoverToEventFlow
  fromEventFlow := heineBorelFiniteSubcoverFromEventFlow

instance heineBorelFiniteSubcoverChapterTasteGate :
    ChapterTasteGate HeineBorelFiniteSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change heineBorelFiniteSubcoverFromEventFlow (heineBorelFiniteSubcoverToEventFlow x) =
      some x
    exact HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_injective heq)

instance heineBorelFiniteSubcoverFieldFaithful :
    FieldFaithful HeineBorelFiniteSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := heineBorelFiniteSubcoverFields
  field_faithful := HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_fields

instance heineBorelFiniteSubcoverNontrivial : Nontrivial HeineBorelFiniteSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HeineBorelFiniteSubcoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HeineBorelFiniteSubcoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HeineBorelFiniteSubcoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heineBorelFiniteSubcoverChapterTasteGate

theorem HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      heineBorelFiniteSubcoverDecodeBHist (heineBorelFiniteSubcoverEncodeBHist h) = h) ∧
      (∀ x : HeineBorelFiniteSubcoverUp,
        heineBorelFiniteSubcoverFromEventFlow (heineBorelFiniteSubcoverToEventFlow x) =
          some x) ∧
        (∀ x y : HeineBorelFiniteSubcoverUp,
          heineBorelFiniteSubcoverToEventFlow x = heineBorelFiniteSubcoverToEventFlow y →
            x = y) ∧
          heineBorelFiniteSubcoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  constructor
  · exact HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HeineBorelFiniteSubcoverTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.HeineBorelFiniteSubcoverUp
