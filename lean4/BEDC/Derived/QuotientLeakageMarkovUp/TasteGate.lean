import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuotientLeakageMarkovUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuotientLeakageMarkovUp : Type where
  | mk (S T O E W H C P N : BHist) : QuotientLeakageMarkovUp
  deriving DecidableEq

def quotientLeakageMarkovEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quotientLeakageMarkovEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quotientLeakageMarkovEncodeBHist h

def quotientLeakageMarkovDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quotientLeakageMarkovDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quotientLeakageMarkovDecodeBHist tail)

private theorem quotientLeakageMarkov_decode_encode_bhist :
    ∀ h : BHist,
      quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quotientLeakageMarkovFields : QuotientLeakageMarkovUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuotientLeakageMarkovUp.mk S T O E W H C P N => [S, T, O, E, W, H, C, P, N]

def quotientLeakageMarkovToEventFlow : QuotientLeakageMarkovUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (quotientLeakageMarkovFields x).map quotientLeakageMarkovEncodeBHist

def quotientLeakageMarkovFromEventFlow : EventFlow → Option QuotientLeakageMarkovUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | O :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
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
                                            (QuotientLeakageMarkovUp.mk
                                              (quotientLeakageMarkovDecodeBHist S)
                                              (quotientLeakageMarkovDecodeBHist T)
                                              (quotientLeakageMarkovDecodeBHist O)
                                              (quotientLeakageMarkovDecodeBHist E)
                                              (quotientLeakageMarkovDecodeBHist W)
                                              (quotientLeakageMarkovDecodeBHist H)
                                              (quotientLeakageMarkovDecodeBHist C)
                                              (quotientLeakageMarkovDecodeBHist P)
                                              (quotientLeakageMarkovDecodeBHist N))
                                      | _ :: _ => none

private theorem quotientLeakageMarkov_round_trip :
    ∀ x : QuotientLeakageMarkovUp,
      quotientLeakageMarkovFromEventFlow (quotientLeakageMarkovToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T O E W H C P N =>
      change
        some
          (QuotientLeakageMarkovUp.mk
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist S))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist T))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist O))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist E))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist W))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist H))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist C))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist P))
            (quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist N))) =
          some (QuotientLeakageMarkovUp.mk S T O E W H C P N)
      rw [quotientLeakageMarkov_decode_encode_bhist S,
        quotientLeakageMarkov_decode_encode_bhist T,
        quotientLeakageMarkov_decode_encode_bhist O,
        quotientLeakageMarkov_decode_encode_bhist E,
        quotientLeakageMarkov_decode_encode_bhist W,
        quotientLeakageMarkov_decode_encode_bhist H,
        quotientLeakageMarkov_decode_encode_bhist C,
        quotientLeakageMarkov_decode_encode_bhist P,
        quotientLeakageMarkov_decode_encode_bhist N]

private theorem quotientLeakageMarkovToEventFlow_injective {x y : QuotientLeakageMarkovUp} :
    quotientLeakageMarkovToEventFlow x = quotientLeakageMarkovToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quotientLeakageMarkovFromEventFlow (quotientLeakageMarkovToEventFlow x) =
        quotientLeakageMarkovFromEventFlow (quotientLeakageMarkovToEventFlow y) :=
    congrArg quotientLeakageMarkovFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (quotientLeakageMarkov_round_trip x).symm
      (Eq.trans hread (quotientLeakageMarkov_round_trip y)))

private theorem quotientLeakageMarkov_fields_faithful :
    ∀ x y : QuotientLeakageMarkovUp,
      quotientLeakageMarkovFields x = quotientLeakageMarkovFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ T₁ O₁ E₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ O₂ E₂ W₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance quotientLeakageMarkovBHistCarrier : BHistCarrier QuotientLeakageMarkovUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quotientLeakageMarkovToEventFlow
  fromEventFlow := quotientLeakageMarkovFromEventFlow

instance quotientLeakageMarkovChapterTasteGate :
    ChapterTasteGate QuotientLeakageMarkovUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quotientLeakageMarkovFromEventFlow (quotientLeakageMarkovToEventFlow x) = some x
    exact quotientLeakageMarkov_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (quotientLeakageMarkovToEventFlow_injective heq)

instance quotientLeakageMarkovFieldFaithful :
    FieldFaithful QuotientLeakageMarkovUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := quotientLeakageMarkovFields
  field_faithful := quotientLeakageMarkov_fields_faithful

instance quotientLeakageMarkovNontrivial : Nontrivial QuotientLeakageMarkovUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuotientLeakageMarkovUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      QuotientLeakageMarkovUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def quotientLeakageMarkovTasteGate : ChapterTasteGate QuotientLeakageMarkovUp :=
  -- BEDC touchpoint anchor: BHist BMark
  quotientLeakageMarkovChapterTasteGate

theorem QuotientLeakageMarkovTasteGate_single_carrier_alignment :
    (∀ h : BHist, quotientLeakageMarkovDecodeBHist (quotientLeakageMarkovEncodeBHist h) = h) ∧
      (∀ x : QuotientLeakageMarkovUp,
        quotientLeakageMarkovFromEventFlow (quotientLeakageMarkovToEventFlow x) = some x) ∧
        (∀ x y : QuotientLeakageMarkovUp,
          quotientLeakageMarkovToEventFlow x = quotientLeakageMarkovToEventFlow y → x = y) ∧
          quotientLeakageMarkovEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨quotientLeakageMarkov_decode_encode_bhist,
      quotientLeakageMarkov_round_trip,
      (fun _ _ heq => quotientLeakageMarkovToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.QuotientLeakageMarkovUp
