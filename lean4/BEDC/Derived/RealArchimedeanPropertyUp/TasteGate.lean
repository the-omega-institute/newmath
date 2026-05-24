import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealArchimedeanPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealArchimedeanPropertyUp : Type where
  | mk (R n q d S G B H C P N : BHist) : RealArchimedeanPropertyUp
  deriving DecidableEq

def realArchimedeanPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realArchimedeanPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realArchimedeanPropertyEncodeBHist h

def realArchimedeanPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realArchimedeanPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realArchimedeanPropertyDecodeBHist tail)

private theorem RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realArchimedeanPropertyFields : RealArchimedeanPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealArchimedeanPropertyUp.mk R n q d S G B H C P N => [R, n, q, d, S, G, B, H, C, P, N]

def realArchimedeanPropertyToEventFlow : RealArchimedeanPropertyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realArchimedeanPropertyFields x).map realArchimedeanPropertyEncodeBHist

def realArchimedeanPropertyFromEventFlow : EventFlow → Option RealArchimedeanPropertyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | n :: rest1 =>
          match rest1 with
          | [] => none
          | q :: rest2 =>
              match rest2 with
              | [] => none
              | d :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | B :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (RealArchimedeanPropertyUp.mk
                                                      (realArchimedeanPropertyDecodeBHist R)
                                                      (realArchimedeanPropertyDecodeBHist n)
                                                      (realArchimedeanPropertyDecodeBHist q)
                                                      (realArchimedeanPropertyDecodeBHist d)
                                                      (realArchimedeanPropertyDecodeBHist S)
                                                      (realArchimedeanPropertyDecodeBHist G)
                                                      (realArchimedeanPropertyDecodeBHist B)
                                                      (realArchimedeanPropertyDecodeBHist H)
                                                      (realArchimedeanPropertyDecodeBHist C)
                                                      (realArchimedeanPropertyDecodeBHist P)
                                                      (realArchimedeanPropertyDecodeBHist N))
                                              | _ :: _ => none

private theorem RealArchimedeanPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealArchimedeanPropertyUp,
      realArchimedeanPropertyFromEventFlow (realArchimedeanPropertyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R n q d S G B H C P N =>
      change
        some
          (RealArchimedeanPropertyUp.mk
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist R))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist n))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist q))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist d))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist S))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist G))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist B))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist H))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist C))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist P))
            (realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist N))) =
          some (RealArchimedeanPropertyUp.mk R n q d S G B H C P N)
      rw [RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode R,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode n,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode q,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode d,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode S,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode G,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode B,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode H,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode C,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode P,
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealArchimedeanPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealArchimedeanPropertyUp} :
    realArchimedeanPropertyToEventFlow x = realArchimedeanPropertyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realArchimedeanPropertyFromEventFlow (realArchimedeanPropertyToEventFlow x) =
        realArchimedeanPropertyFromEventFlow (realArchimedeanPropertyToEventFlow y) :=
    congrArg realArchimedeanPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealArchimedeanPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealArchimedeanPropertyTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealArchimedeanPropertyTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealArchimedeanPropertyUp,
      realArchimedeanPropertyFields x = realArchimedeanPropertyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ n₁ q₁ d₁ S₁ G₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ n₂ q₂ d₂ S₂ G₂ B₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hn tail1
          injection tail1 with hq tail2
          injection tail2 with hd tail3
          injection tail3 with hS tail4
          injection tail4 with hG tail5
          injection tail5 with hB tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hR
          subst hn
          subst hq
          subst hd
          subst hS
          subst hG
          subst hB
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realArchimedeanPropertyBHistCarrier : BHistCarrier RealArchimedeanPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realArchimedeanPropertyToEventFlow
  fromEventFlow := realArchimedeanPropertyFromEventFlow

instance realArchimedeanPropertyChapterTasteGate :
    ChapterTasteGate RealArchimedeanPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realArchimedeanPropertyFromEventFlow (realArchimedeanPropertyToEventFlow x) = some x
    exact RealArchimedeanPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealArchimedeanPropertyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realArchimedeanPropertyFieldFaithful : FieldFaithful RealArchimedeanPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realArchimedeanPropertyFields
  field_faithful := RealArchimedeanPropertyTasteGate_single_carrier_alignment_fields_faithful

instance realArchimedeanPropertyNontrivial : Nontrivial RealArchimedeanPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealArchimedeanPropertyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealArchimedeanPropertyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealArchimedeanPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realArchimedeanPropertyDecodeBHist (realArchimedeanPropertyEncodeBHist h) = h) ∧
      (∀ x : RealArchimedeanPropertyUp,
        realArchimedeanPropertyFromEventFlow (realArchimedeanPropertyToEventFlow x) = some x) ∧
        (∀ x y : RealArchimedeanPropertyUp,
          realArchimedeanPropertyToEventFlow x = realArchimedeanPropertyToEventFlow y →
            x = y) ∧
          realArchimedeanPropertyEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RealArchimedeanPropertyUp,
              realArchimedeanPropertyFields x = realArchimedeanPropertyFields y → x = y) ∧
              (∃ x y : RealArchimedeanPropertyUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RealArchimedeanPropertyTasteGate_single_carrier_alignment_decode_encode,
      RealArchimedeanPropertyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealArchimedeanPropertyTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      RealArchimedeanPropertyTasteGate_single_carrier_alignment_fields_faithful,
      ⟨RealArchimedeanPropertyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        RealArchimedeanPropertyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.RealArchimedeanPropertyUp
