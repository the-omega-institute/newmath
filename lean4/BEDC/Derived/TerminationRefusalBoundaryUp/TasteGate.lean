import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TerminationRefusalBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TerminationRefusalBoundaryUp : Type where
  | mk (S I T F U H C P N : BHist) : TerminationRefusalBoundaryUp
  deriving DecidableEq

def terminationRefusalBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: terminationRefusalBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: terminationRefusalBoundaryEncodeBHist h

def terminationRefusalBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (terminationRefusalBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (terminationRefusalBoundaryDecodeBHist tail)

private theorem terminationRefusalBoundary_decode_encode_bhist :
    ∀ h : BHist,
      terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def terminationRefusalBoundaryFields : TerminationRefusalBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TerminationRefusalBoundaryUp.mk S I T F U H C P N => [S, I, T, F, U, H, C, P, N]

def terminationRefusalBoundaryToEventFlow : TerminationRefusalBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map terminationRefusalBoundaryEncodeBHist (terminationRefusalBoundaryFields x)

def terminationRefusalBoundaryFromEventFlow : EventFlow → Option TerminationRefusalBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | U :: rest4 =>
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
                                            (TerminationRefusalBoundaryUp.mk
                                              (terminationRefusalBoundaryDecodeBHist S)
                                              (terminationRefusalBoundaryDecodeBHist I)
                                              (terminationRefusalBoundaryDecodeBHist T)
                                              (terminationRefusalBoundaryDecodeBHist F)
                                              (terminationRefusalBoundaryDecodeBHist U)
                                              (terminationRefusalBoundaryDecodeBHist H)
                                              (terminationRefusalBoundaryDecodeBHist C)
                                              (terminationRefusalBoundaryDecodeBHist P)
                                              (terminationRefusalBoundaryDecodeBHist N))
                                      | _head :: _tail => none

private theorem terminationRefusalBoundary_round_trip :
    ∀ x : TerminationRefusalBoundaryUp,
      terminationRefusalBoundaryFromEventFlow
          (terminationRefusalBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S I T F U H C P N =>
      change
        some
          (TerminationRefusalBoundaryUp.mk
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist S))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist I))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist T))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist F))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist U))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist H))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist C))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist P))
            (terminationRefusalBoundaryDecodeBHist (terminationRefusalBoundaryEncodeBHist N))) =
          some (TerminationRefusalBoundaryUp.mk S I T F U H C P N)
      rw [terminationRefusalBoundary_decode_encode_bhist S,
        terminationRefusalBoundary_decode_encode_bhist I,
        terminationRefusalBoundary_decode_encode_bhist T,
        terminationRefusalBoundary_decode_encode_bhist F,
        terminationRefusalBoundary_decode_encode_bhist U,
        terminationRefusalBoundary_decode_encode_bhist H,
        terminationRefusalBoundary_decode_encode_bhist C,
        terminationRefusalBoundary_decode_encode_bhist P,
        terminationRefusalBoundary_decode_encode_bhist N]

private theorem terminationRefusalBoundaryToEventFlow_injective
    {x y : TerminationRefusalBoundaryUp} :
    terminationRefusalBoundaryToEventFlow x = terminationRefusalBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      terminationRefusalBoundaryFromEventFlow (terminationRefusalBoundaryToEventFlow x) =
        terminationRefusalBoundaryFromEventFlow (terminationRefusalBoundaryToEventFlow y) :=
    congrArg terminationRefusalBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (terminationRefusalBoundary_round_trip x).symm
      (Eq.trans hread (terminationRefusalBoundary_round_trip y)))

private theorem terminationRefusalBoundary_field_faithful :
    ∀ x y : TerminationRefusalBoundaryUp,
      terminationRefusalBoundaryFields x = terminationRefusalBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ I₁ T₁ F₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ I₂ T₂ F₂ U₂ H₂ C₂ P₂ N₂ =>
          injection h with hS t1
          injection t1 with hI t2
          injection t2 with hT t3
          injection t3 with hF t4
          injection t4 with hU t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          cases hS
          cases hI
          cases hT
          cases hF
          cases hU
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance terminationRefusalBoundaryBHistCarrier :
    BHistCarrier TerminationRefusalBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := terminationRefusalBoundaryToEventFlow
  fromEventFlow := terminationRefusalBoundaryFromEventFlow

instance terminationRefusalBoundaryChapterTasteGate :
    ChapterTasteGate TerminationRefusalBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      terminationRefusalBoundaryFromEventFlow
        (terminationRefusalBoundaryToEventFlow x) = some x
    exact terminationRefusalBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (terminationRefusalBoundaryToEventFlow_injective heq)

instance terminationRefusalBoundaryFieldFaithful :
    FieldFaithful TerminationRefusalBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := terminationRefusalBoundaryFields
  field_faithful := terminationRefusalBoundary_field_faithful

instance terminationRefusalBoundaryNontrivial :
    Nontrivial TerminationRefusalBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TerminationRefusalBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TerminationRefusalBoundaryUp.mk BHist.Empty BHist.Empty (BHist.e0 BHist.Empty)
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TerminationRefusalBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  terminationRefusalBoundaryChapterTasteGate

theorem TerminationRefusalBoundaryTasteGate_single_carrier_alignment :
    terminationRefusalBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      terminationRefusalBoundaryEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ h : BHist,
          terminationRefusalBoundaryDecodeBHist
            (terminationRefusalBoundaryEncodeBHist h) = h) ∧
          (∀ x : TerminationRefusalBoundaryUp,
            terminationRefusalBoundaryFromEventFlow
              (terminationRefusalBoundaryToEventFlow x) = some x) ∧
            (∀ x y : TerminationRefusalBoundaryUp,
              terminationRefusalBoundaryToEventFlow x =
                terminationRefusalBoundaryToEventFlow y → x = y) ∧
              Nonempty (BHistCarrier TerminationRefusalBoundaryUp) ∧
                Nonempty (FieldFaithful TerminationRefusalBoundaryUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact terminationRefusalBoundary_decode_encode_bhist
      · constructor
        · exact terminationRefusalBoundary_round_trip
        · constructor
          · intro x y heq
            exact terminationRefusalBoundaryToEventFlow_injective heq
          · constructor
            · exact ⟨terminationRefusalBoundaryBHistCarrier⟩
            · exact ⟨terminationRefusalBoundaryFieldFaithful⟩

end BEDC.Derived.TerminationRefusalBoundaryUp
