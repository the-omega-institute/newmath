import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCriterionUp : Type where
  | mk :
      (window modulus tail tolerance realSeal transport route provenance localCert : BHist) →
      CauchyCriterionUp
  deriving DecidableEq

def cauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCriterionEncodeBHist h

def cauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCriterionDecodeBHist tail)

private theorem cauchyCriterion_decode_encode_bhist :
    ∀ h : BHist, cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCriterionFields : CauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCriterionUp.mk window modulus tail tolerance realSeal transport route provenance
      localCert =>
      [window, modulus, tail, tolerance, realSeal, transport, route, provenance, localCert]

def cauchyCriterionToEventFlow : CauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCriterionFields x).map cauchyCriterionEncodeBHist

def cauchyCriterionFromEventFlow : EventFlow → Option CauchyCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | window :: rest0 =>
      match rest0 with
      | [] => none
      | modulus :: rest1 =>
          match rest1 with
          | [] => none
          | tail :: rest2 =>
              match rest2 with
              | [] => none
              | tolerance :: rest3 =>
                  match rest3 with
                  | [] => none
                  | realSeal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CauchyCriterionUp.mk
                                              (cauchyCriterionDecodeBHist window)
                                              (cauchyCriterionDecodeBHist modulus)
                                              (cauchyCriterionDecodeBHist tail)
                                              (cauchyCriterionDecodeBHist tolerance)
                                              (cauchyCriterionDecodeBHist realSeal)
                                              (cauchyCriterionDecodeBHist transport)
                                              (cauchyCriterionDecodeBHist route)
                                              (cauchyCriterionDecodeBHist provenance)
                                              (cauchyCriterionDecodeBHist localCert))
                                      | _ :: _ => none

private theorem cauchyCriterion_round_trip :
    ∀ x : CauchyCriterionUp,
      cauchyCriterionFromEventFlow (cauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window modulus tail tolerance realSeal transport route provenance localCert =>
      change
        some
          (CauchyCriterionUp.mk
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist window))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist modulus))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist tail))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist tolerance))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist realSeal))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist transport))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist route))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist provenance))
            (cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist localCert))) =
          some
            (CauchyCriterionUp.mk window modulus tail tolerance realSeal transport route
              provenance localCert)
      rw [cauchyCriterion_decode_encode_bhist window,
        cauchyCriterion_decode_encode_bhist modulus,
        cauchyCriterion_decode_encode_bhist tail,
        cauchyCriterion_decode_encode_bhist tolerance,
        cauchyCriterion_decode_encode_bhist realSeal,
        cauchyCriterion_decode_encode_bhist transport,
        cauchyCriterion_decode_encode_bhist route,
        cauchyCriterion_decode_encode_bhist provenance,
        cauchyCriterion_decode_encode_bhist localCert]

private theorem cauchyCriterionToEventFlow_injective {x y : CauchyCriterionUp} :
    cauchyCriterionToEventFlow x = cauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCriterionFromEventFlow (cauchyCriterionToEventFlow x) =
        cauchyCriterionFromEventFlow (cauchyCriterionToEventFlow y) :=
    congrArg cauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCriterion_round_trip x).symm
      (Eq.trans hread (cauchyCriterion_round_trip y)))

private theorem cauchyCriterion_field_faithful :
    ∀ x y : CauchyCriterionUp, cauchyCriterionFields x = cauchyCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk window₁ modulus₁ tail₁ tolerance₁ realSeal₁ transport₁ route₁ provenance₁
      localCert₁ =>
      cases y with
      | mk window₂ modulus₂ tail₂ tolerance₂ realSeal₂ transport₂ route₂ provenance₂
          localCert₂ =>
          cases h
          rfl

instance cauchyCriterionBHistCarrier : BHistCarrier CauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCriterionToEventFlow
  fromEventFlow := cauchyCriterionFromEventFlow

instance cauchyCriterionChapterTasteGate : ChapterTasteGate CauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCriterionFromEventFlow (cauchyCriterionToEventFlow x) = some x
    exact cauchyCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCriterionToEventFlow_injective heq)

instance cauchyCriterionFieldFaithful : FieldFaithful CauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCriterionFields
  field_faithful := cauchyCriterion_field_faithful

instance cauchyCriterionNontrivial : Nontrivial CauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCriterionChapterTasteGate

theorem CauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCriterionDecodeBHist (cauchyCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyCriterionUp,
        cauchyCriterionFromEventFlow (cauchyCriterionToEventFlow x) = some x) ∧
        (∀ x y : CauchyCriterionUp,
          cauchyCriterionToEventFlow x = cauchyCriterionToEventFlow y -> x = y) ∧
          cauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyCriterion_decode_encode_bhist
  · constructor
    · exact cauchyCriterion_round_trip
    · constructor
      · intro x y heq
        exact cauchyCriterionToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyCriterionUp
