import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuntimeTruthSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuntimeTruthSeparationUp : Type where
  | mk :
      (structural runtimeRequest truthRequest refusalLedger transport continuation provenance
        nameCert : BHist) →
      RuntimeTruthSeparationUp

def runtimeTruthSeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: runtimeTruthSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: runtimeTruthSeparationEncodeBHist h

def runtimeTruthSeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (runtimeTruthSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (runtimeTruthSeparationDecodeBHist tail)

private theorem runtimeTruthSeparation_decode_encode_bhist :
    ∀ h : BHist,
      runtimeTruthSeparationDecodeBHist (runtimeTruthSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def runtimeTruthSeparationFields : RuntimeTruthSeparationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RuntimeTruthSeparationUp.mk structural runtimeRequest truthRequest refusalLedger transport
      continuation provenance nameCert =>
      [structural, runtimeRequest, truthRequest, refusalLedger, transport, continuation,
        provenance, nameCert]

def runtimeTruthSeparationToEventFlow : RuntimeTruthSeparationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (runtimeTruthSeparationFields x).map runtimeTruthSeparationEncodeBHist

def runtimeTruthSeparationFromEventFlow : EventFlow → Option RuntimeTruthSeparationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | structural :: rest0 =>
      match rest0 with
      | [] => none
      | runtimeRequest :: rest1 =>
          match rest1 with
          | [] => none
          | truthRequest :: rest2 =>
              match rest2 with
              | [] => none
              | refusalLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | continuation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | nameCert :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (RuntimeTruthSeparationUp.mk
                                          (runtimeTruthSeparationDecodeBHist structural)
                                          (runtimeTruthSeparationDecodeBHist runtimeRequest)
                                          (runtimeTruthSeparationDecodeBHist truthRequest)
                                          (runtimeTruthSeparationDecodeBHist refusalLedger)
                                          (runtimeTruthSeparationDecodeBHist transport)
                                          (runtimeTruthSeparationDecodeBHist continuation)
                                          (runtimeTruthSeparationDecodeBHist provenance)
                                          (runtimeTruthSeparationDecodeBHist nameCert))
                                  | _ :: _ => none

private theorem runtimeTruthSeparation_round_trip :
    ∀ x : RuntimeTruthSeparationUp,
      runtimeTruthSeparationFromEventFlow
        (runtimeTruthSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk structural runtimeRequest truthRequest refusalLedger transport continuation provenance
      nameCert =>
      change
        some
          (RuntimeTruthSeparationUp.mk
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist structural))
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist runtimeRequest))
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist truthRequest))
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist refusalLedger))
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist transport))
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist continuation))
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist provenance))
            (runtimeTruthSeparationDecodeBHist
              (runtimeTruthSeparationEncodeBHist nameCert))) =
          some
            (RuntimeTruthSeparationUp.mk structural runtimeRequest truthRequest refusalLedger
              transport continuation provenance nameCert)
      rw [runtimeTruthSeparation_decode_encode_bhist structural,
        runtimeTruthSeparation_decode_encode_bhist runtimeRequest,
        runtimeTruthSeparation_decode_encode_bhist truthRequest,
        runtimeTruthSeparation_decode_encode_bhist refusalLedger,
        runtimeTruthSeparation_decode_encode_bhist transport,
        runtimeTruthSeparation_decode_encode_bhist continuation,
        runtimeTruthSeparation_decode_encode_bhist provenance,
        runtimeTruthSeparation_decode_encode_bhist nameCert]

private theorem runtimeTruthSeparationToEventFlow_injective
    {x y : RuntimeTruthSeparationUp} :
    runtimeTruthSeparationToEventFlow x = runtimeTruthSeparationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      runtimeTruthSeparationFromEventFlow (runtimeTruthSeparationToEventFlow x) =
        runtimeTruthSeparationFromEventFlow (runtimeTruthSeparationToEventFlow y) :=
    congrArg runtimeTruthSeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (runtimeTruthSeparation_round_trip x).symm
      (Eq.trans hread (runtimeTruthSeparation_round_trip y)))

private theorem runtimeTruthSeparation_fields_faithful :
    ∀ x y : RuntimeTruthSeparationUp,
      runtimeTruthSeparationFields x = runtimeTruthSeparationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk structural₁ runtimeRequest₁ truthRequest₁ refusalLedger₁ transport₁ continuation₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk structural₂ runtimeRequest₂ truthRequest₂ refusalLedger₂ transport₂ continuation₂
          provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance runtimeTruthSeparationBHistCarrier :
    BHistCarrier RuntimeTruthSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := runtimeTruthSeparationToEventFlow
  fromEventFlow := runtimeTruthSeparationFromEventFlow

instance runtimeTruthSeparationChapterTasteGate :
    ChapterTasteGate RuntimeTruthSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      runtimeTruthSeparationFromEventFlow
        (runtimeTruthSeparationToEventFlow x) = some x
    exact runtimeTruthSeparation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (runtimeTruthSeparationToEventFlow_injective heq)

instance runtimeTruthSeparationFieldFaithful :
    FieldFaithful RuntimeTruthSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := runtimeTruthSeparationFields
  field_faithful := runtimeTruthSeparation_fields_faithful

instance runtimeTruthSeparationNontrivial :
    Nontrivial RuntimeTruthSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RuntimeTruthSeparationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RuntimeTruthSeparationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RuntimeTruthSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  runtimeTruthSeparationChapterTasteGate

theorem RuntimeTruthSeparationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      runtimeTruthSeparationDecodeBHist (runtimeTruthSeparationEncodeBHist h) = h) ∧
      (∀ x : RuntimeTruthSeparationUp,
        runtimeTruthSeparationFromEventFlow
          (runtimeTruthSeparationToEventFlow x) = some x) ∧
        (∀ x y : RuntimeTruthSeparationUp,
          runtimeTruthSeparationToEventFlow x = runtimeTruthSeparationToEventFlow y ->
            x = y) ∧
          runtimeTruthSeparationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨runtimeTruthSeparation_decode_encode_bhist, runtimeTruthSeparation_round_trip,
      fun x y heq => runtimeTruthSeparationToEventFlow_injective heq, rfl⟩

end BEDC.Derived.RuntimeTruthSeparationUp
