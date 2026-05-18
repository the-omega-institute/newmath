import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationBisimulationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationBisimulationUp : Type where
  | mk
      (left right forward backward endpoint transport replay provenance localName : BHist) :
      ContinuationBisimulationUp
  deriving DecidableEq

def continuationBisimulationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationBisimulationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationBisimulationEncodeBHist h

def continuationBisimulationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationBisimulationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationBisimulationDecodeBHist tail)

private theorem continuationBisimulationDecode_encode_bhist :
    ∀ h : BHist,
      continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuationBisimulationFields : ContinuationBisimulationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationBisimulationUp.mk left right forward backward endpoint transport replay
      provenance localName =>
      [left, right, forward, backward, endpoint, transport, replay, provenance, localName]

def continuationBisimulationToEventFlow : ContinuationBisimulationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (continuationBisimulationFields x).map continuationBisimulationEncodeBHist

def continuationBisimulationFromEventFlow : EventFlow → Option ContinuationBisimulationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | left :: rest0 =>
      match rest0 with
      | [] => none
      | right :: rest1 =>
          match rest1 with
          | [] => none
          | forward :: rest2 =>
              match rest2 with
              | [] => none
              | backward :: rest3 =>
                  match rest3 with
                  | [] => none
                  | endpoint :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ContinuationBisimulationUp.mk
                                              (continuationBisimulationDecodeBHist left)
                                              (continuationBisimulationDecodeBHist right)
                                              (continuationBisimulationDecodeBHist forward)
                                              (continuationBisimulationDecodeBHist backward)
                                              (continuationBisimulationDecodeBHist endpoint)
                                              (continuationBisimulationDecodeBHist transport)
                                              (continuationBisimulationDecodeBHist replay)
                                              (continuationBisimulationDecodeBHist provenance)
                                              (continuationBisimulationDecodeBHist localName))
                                      | _ :: _ => none

private theorem continuationBisimulation_round_trip :
    ∀ x : ContinuationBisimulationUp,
      continuationBisimulationFromEventFlow (continuationBisimulationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right forward backward endpoint transport replay provenance localName =>
      change
        some
          (ContinuationBisimulationUp.mk
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist left))
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist right))
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist forward))
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist backward))
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist endpoint))
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist transport))
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist replay))
            (continuationBisimulationDecodeBHist (continuationBisimulationEncodeBHist provenance))
            (continuationBisimulationDecodeBHist
              (continuationBisimulationEncodeBHist localName))) =
          some
            (ContinuationBisimulationUp.mk left right forward backward endpoint transport replay
              provenance localName)
      rw [continuationBisimulationDecode_encode_bhist left,
        continuationBisimulationDecode_encode_bhist right,
        continuationBisimulationDecode_encode_bhist forward,
        continuationBisimulationDecode_encode_bhist backward,
        continuationBisimulationDecode_encode_bhist endpoint,
        continuationBisimulationDecode_encode_bhist transport,
        continuationBisimulationDecode_encode_bhist replay,
        continuationBisimulationDecode_encode_bhist provenance,
        continuationBisimulationDecode_encode_bhist localName]

private theorem continuationBisimulationToEventFlow_injective {x y : ContinuationBisimulationUp} :
    continuationBisimulationToEventFlow x = continuationBisimulationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationBisimulationFromEventFlow (continuationBisimulationToEventFlow x) =
        continuationBisimulationFromEventFlow (continuationBisimulationToEventFlow y) :=
    congrArg continuationBisimulationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (continuationBisimulation_round_trip x).symm
      (Eq.trans hread (continuationBisimulation_round_trip y)))

private theorem continuationBisimulation_fields_faithful :
    ∀ x y : ContinuationBisimulationUp,
      continuationBisimulationFields x = continuationBisimulationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk left₁ right₁ forward₁ backward₁ endpoint₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk left₂ right₂ forward₂ backward₂ endpoint₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance continuationBisimulationBHistCarrier : BHistCarrier ContinuationBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationBisimulationToEventFlow
  fromEventFlow := continuationBisimulationFromEventFlow

instance continuationBisimulationChapterTasteGate :
    ChapterTasteGate ContinuationBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      continuationBisimulationFromEventFlow (continuationBisimulationToEventFlow x) =
        some x
    exact continuationBisimulation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuationBisimulationToEventFlow_injective heq)

instance continuationBisimulationFieldFaithful : FieldFaithful ContinuationBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := continuationBisimulationFields
  field_faithful := continuationBisimulation_fields_faithful

instance continuationBisimulationNontrivial : Nontrivial ContinuationBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuationBisimulationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContinuationBisimulationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContinuationBisimulationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuationBisimulationChapterTasteGate

namespace TasteGate

theorem ContinuationBisimulationNameCertObligations
    {left right forward backward endpoint transport replay provenance localName : BHist} :
    continuationBisimulationFields
        (ContinuationBisimulationUp.mk left right forward backward endpoint transport replay
          provenance localName) =
        [left, right, forward, backward, endpoint, transport, replay, provenance,
          localName] ∧
      continuationBisimulationDecodeBHist
          (continuationBisimulationEncodeBHist localName) =
        localName ∧
        Nonempty (ChapterTasteGate ContinuationBisimulationUp) ∧
          continuationBisimulationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · rfl
  · constructor
    · exact continuationBisimulationDecode_encode_bhist localName
    · constructor
      · exact ⟨continuationBisimulationChapterTasteGate⟩
      · rfl

def taste_gate : ChapterTasteGate ContinuationBisimulationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.ContinuationBisimulationUp.taste_gate

end TasteGate

end BEDC.Derived.ContinuationBisimulationUp
