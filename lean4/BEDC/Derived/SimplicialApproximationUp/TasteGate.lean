import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SimplicialApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SimplicialApproximationUp : Type where
  | mk (K L S V F T B M H C P N : BHist) : SimplicialApproximationUp
  deriving DecidableEq

def simplicialApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: simplicialApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: simplicialApproximationEncodeBHist h

def simplicialApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (simplicialApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (simplicialApproximationDecodeBHist tail)

private theorem simplicialApproximationDecode_encode_bhist :
    ∀ h : BHist, simplicialApproximationDecodeBHist
      (simplicialApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def simplicialApproximationFields : SimplicialApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SimplicialApproximationUp.mk K L S V F T B M H C P N =>
      [K, L, S, V, F, T, B, M, H, C, P, N]

def simplicialApproximationToEventFlow : SimplicialApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (simplicialApproximationFields x).map simplicialApproximationEncodeBHist

def simplicialApproximationFromEventFlow : EventFlow → Option SimplicialApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | V :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | B :: rest6 =>
                              match rest6 with
                              | [] => none
                              | M :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (SimplicialApproximationUp.mk
                                                          (simplicialApproximationDecodeBHist K)
                                                          (simplicialApproximationDecodeBHist L)
                                                          (simplicialApproximationDecodeBHist S)
                                                          (simplicialApproximationDecodeBHist V)
                                                          (simplicialApproximationDecodeBHist F)
                                                          (simplicialApproximationDecodeBHist T)
                                                          (simplicialApproximationDecodeBHist B)
                                                          (simplicialApproximationDecodeBHist M)
                                                          (simplicialApproximationDecodeBHist H)
                                                          (simplicialApproximationDecodeBHist C)
                                                          (simplicialApproximationDecodeBHist P)
                                                          (simplicialApproximationDecodeBHist N))
                                                  | _ :: _ => none

private theorem simplicialApproximation_round_trip :
    ∀ x : SimplicialApproximationUp,
      simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K L S V F T B M H C P N =>
      change
        some
          (SimplicialApproximationUp.mk
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist K))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist L))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist S))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist V))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist F))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist T))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist B))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist M))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist H))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist C))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist P))
            (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist N))) =
          some (SimplicialApproximationUp.mk K L S V F T B M H C P N)
      rw [simplicialApproximationDecode_encode_bhist K,
        simplicialApproximationDecode_encode_bhist L,
        simplicialApproximationDecode_encode_bhist S,
        simplicialApproximationDecode_encode_bhist V,
        simplicialApproximationDecode_encode_bhist F,
        simplicialApproximationDecode_encode_bhist T,
        simplicialApproximationDecode_encode_bhist B,
        simplicialApproximationDecode_encode_bhist M,
        simplicialApproximationDecode_encode_bhist H,
        simplicialApproximationDecode_encode_bhist C,
        simplicialApproximationDecode_encode_bhist P,
        simplicialApproximationDecode_encode_bhist N]

private theorem simplicialApproximationToEventFlow_injective
    {x y : SimplicialApproximationUp} :
    simplicialApproximationToEventFlow x = simplicialApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
        simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow y) :=
    congrArg simplicialApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (simplicialApproximation_round_trip x).symm
      (Eq.trans hread (simplicialApproximation_round_trip y)))

private theorem simplicialApproximation_fields_faithful :
    ∀ x y : SimplicialApproximationUp,
      simplicialApproximationFields x = simplicialApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 L1 S1 V1 F1 T1 B1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 L2 S2 V2 F2 T2 B2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance simplicialApproximationBHistCarrier : BHistCarrier SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := simplicialApproximationToEventFlow
  fromEventFlow := simplicialApproximationFromEventFlow

instance simplicialApproximationChapterTasteGate :
    ChapterTasteGate SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
        some x
    exact simplicialApproximation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (simplicialApproximationToEventFlow_injective heq)

instance simplicialApproximationFieldFaithful : FieldFaithful SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := simplicialApproximationFields
  field_faithful := simplicialApproximation_fields_faithful

instance simplicialApproximationNontrivial : Nontrivial SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SimplicialApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SimplicialApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SimplicialApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SimplicialApproximationUp) ∧
      Nonempty (FieldFaithful SimplicialApproximationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SimplicialApproximationUp) ∧
          (∀ h : BHist,
            simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist h) =
              h) ∧
            (∀ x : SimplicialApproximationUp,
              simplicialApproximationFromEventFlow
                (simplicialApproximationToEventFlow x) = some x) ∧
              simplicialApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨simplicialApproximationChapterTasteGate⟩
  · constructor
    · exact ⟨simplicialApproximationFieldFaithful⟩
    · constructor
      · exact ⟨simplicialApproximationNontrivial⟩
      · constructor
        · exact simplicialApproximationDecode_encode_bhist
        · constructor
          · exact simplicialApproximation_round_trip
          · rfl

end BEDC.Derived.SimplicialApproximationUp
