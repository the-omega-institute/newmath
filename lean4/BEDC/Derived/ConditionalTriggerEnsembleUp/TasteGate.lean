import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConditionalTriggerEnsembleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConditionalTriggerEnsembleUp : Type where
  | mk (T B Q Z M L A H C P N : BHist) : ConditionalTriggerEnsembleUp
  deriving DecidableEq

def conditionalTriggerEnsembleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: conditionalTriggerEnsembleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: conditionalTriggerEnsembleEncodeBHist h

def conditionalTriggerEnsembleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (conditionalTriggerEnsembleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (conditionalTriggerEnsembleDecodeBHist tail)

private theorem conditionalTriggerEnsemble_decode_encode_bhist :
    ∀ h : BHist,
      conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def conditionalTriggerEnsembleFields : ConditionalTriggerEnsembleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConditionalTriggerEnsembleUp.mk T B Q Z M L A H C P N => [T, B, Q, Z, M, L, A, H, C, P, N]

def conditionalTriggerEnsembleToEventFlow : ConditionalTriggerEnsembleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map conditionalTriggerEnsembleEncodeBHist (conditionalTriggerEnsembleFields x)

def conditionalTriggerEnsembleFromEventFlow : EventFlow → Option ConditionalTriggerEnsembleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | Z :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | A :: rest6 =>
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
                                                    (ConditionalTriggerEnsembleUp.mk
                                                      (conditionalTriggerEnsembleDecodeBHist T)
                                                      (conditionalTriggerEnsembleDecodeBHist B)
                                                      (conditionalTriggerEnsembleDecodeBHist Q)
                                                      (conditionalTriggerEnsembleDecodeBHist Z)
                                                      (conditionalTriggerEnsembleDecodeBHist M)
                                                      (conditionalTriggerEnsembleDecodeBHist L)
                                                      (conditionalTriggerEnsembleDecodeBHist A)
                                                      (conditionalTriggerEnsembleDecodeBHist H)
                                                      (conditionalTriggerEnsembleDecodeBHist C)
                                                      (conditionalTriggerEnsembleDecodeBHist P)
                                                      (conditionalTriggerEnsembleDecodeBHist N))
                                              | _ :: _ => none

private theorem conditionalTriggerEnsemble_round_trip :
    ∀ x : ConditionalTriggerEnsembleUp,
      conditionalTriggerEnsembleFromEventFlow
        (conditionalTriggerEnsembleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B Q Z M L A H C P N =>
      change
        some
          (ConditionalTriggerEnsembleUp.mk
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist T))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist B))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist Q))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist Z))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist M))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist L))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist A))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist H))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist C))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist P))
            (conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist N))) =
          some (ConditionalTriggerEnsembleUp.mk T B Q Z M L A H C P N)
      rw [conditionalTriggerEnsemble_decode_encode_bhist T,
        conditionalTriggerEnsemble_decode_encode_bhist B,
        conditionalTriggerEnsemble_decode_encode_bhist Q,
        conditionalTriggerEnsemble_decode_encode_bhist Z,
        conditionalTriggerEnsemble_decode_encode_bhist M,
        conditionalTriggerEnsemble_decode_encode_bhist L,
        conditionalTriggerEnsemble_decode_encode_bhist A,
        conditionalTriggerEnsemble_decode_encode_bhist H,
        conditionalTriggerEnsemble_decode_encode_bhist C,
        conditionalTriggerEnsemble_decode_encode_bhist P,
        conditionalTriggerEnsemble_decode_encode_bhist N]

private theorem conditionalTriggerEnsembleToEventFlow_injective
    {x y : ConditionalTriggerEnsembleUp} :
    conditionalTriggerEnsembleToEventFlow x = conditionalTriggerEnsembleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      conditionalTriggerEnsembleFromEventFlow (conditionalTriggerEnsembleToEventFlow x) =
        conditionalTriggerEnsembleFromEventFlow (conditionalTriggerEnsembleToEventFlow y) :=
    congrArg conditionalTriggerEnsembleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (conditionalTriggerEnsemble_round_trip x).symm
      (Eq.trans hread (conditionalTriggerEnsemble_round_trip y)))

private theorem conditionalTriggerEnsemble_field_faithful :
    ∀ x y : ConditionalTriggerEnsembleUp,
      conditionalTriggerEnsembleFields x = conditionalTriggerEnsembleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T₁ B₁ Q₁ Z₁ M₁ L₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ B₂ Q₂ Z₂ M₂ L₂ A₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance conditionalTriggerEnsembleBHistCarrier :
    BHistCarrier ConditionalTriggerEnsembleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := conditionalTriggerEnsembleToEventFlow
  fromEventFlow := conditionalTriggerEnsembleFromEventFlow

instance conditionalTriggerEnsembleChapterTasteGate :
    ChapterTasteGate ConditionalTriggerEnsembleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      conditionalTriggerEnsembleFromEventFlow
        (conditionalTriggerEnsembleToEventFlow x) = some x
    exact conditionalTriggerEnsemble_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (conditionalTriggerEnsembleToEventFlow_injective heq)

instance conditionalTriggerEnsembleFieldFaithful :
    FieldFaithful ConditionalTriggerEnsembleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := conditionalTriggerEnsembleFields
  field_faithful := conditionalTriggerEnsemble_field_faithful

instance conditionalTriggerEnsembleNontrivial :
    Nontrivial ConditionalTriggerEnsembleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConditionalTriggerEnsembleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConditionalTriggerEnsembleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConditionalTriggerEnsembleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  conditionalTriggerEnsembleChapterTasteGate

theorem ConditionalTriggerEnsembleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      conditionalTriggerEnsembleDecodeBHist (conditionalTriggerEnsembleEncodeBHist h) = h) ∧
      (∀ x : ConditionalTriggerEnsembleUp,
        conditionalTriggerEnsembleFromEventFlow
          (conditionalTriggerEnsembleToEventFlow x) = some x) ∧
        (∀ x y : ConditionalTriggerEnsembleUp,
          conditionalTriggerEnsembleToEventFlow x = conditionalTriggerEnsembleToEventFlow y →
            x = y) ∧
          conditionalTriggerEnsembleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact conditionalTriggerEnsemble_decode_encode_bhist
  · constructor
    · exact conditionalTriggerEnsemble_round_trip
    · constructor
      · intro x y heq
        exact conditionalTriggerEnsembleToEventFlow_injective heq
      · rfl

end BEDC.Derived.ConditionalTriggerEnsembleUp
