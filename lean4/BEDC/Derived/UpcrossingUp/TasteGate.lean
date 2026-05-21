import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpcrossingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpcrossingUp : Type where
  | mk (omega martingale lower upper horizon values lowerLedger upperLedger transport routes
      provenance nameCert : BHist) : UpcrossingUp
  deriving DecidableEq

def upcrossingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upcrossingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upcrossingEncodeBHist h

def upcrossingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upcrossingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upcrossingDecodeBHist tail)

private theorem upcrossingDecode_encode_bhist :
    ∀ h : BHist, upcrossingDecodeBHist (upcrossingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def upcrossingFields : UpcrossingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpcrossingUp.mk omega martingale lower upper horizon values lowerLedger upperLedger
      transport routes provenance nameCert =>
      [omega, martingale, lower, upper, horizon, values, lowerLedger, upperLedger,
        transport, routes, provenance, nameCert]

def upcrossingToEventFlow : UpcrossingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (upcrossingFields x).map upcrossingEncodeBHist

def upcrossingFromEventFlow (flow : EventFlow) : Option UpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | omega :: rest₁ =>
      match rest₁ with
      | [] => none
      | martingale :: rest₂ =>
          match rest₂ with
          | [] => none
          | lower :: rest₃ =>
              match rest₃ with
              | [] => none
              | upper :: rest₄ =>
                  match rest₄ with
                  | [] => none
                  | horizon :: rest₅ =>
                      match rest₅ with
                      | [] => none
                      | values :: rest₆ =>
                          match rest₆ with
                          | [] => none
                          | lowerLedger :: rest₇ =>
                              match rest₇ with
                              | [] => none
                              | upperLedger :: rest₈ =>
                                  match rest₈ with
                                  | [] => none
                                  | transport :: rest₉ =>
                                      match rest₉ with
                                      | [] => none
                                      | routes :: rest₁₀ =>
                                          match rest₁₀ with
                                          | [] => none
                                          | provenance :: rest₁₁ =>
                                              match rest₁₁ with
                                              | [] => none
                                              | nameCert :: rest₁₂ =>
                                                  match rest₁₂ with
                                                  | [] =>
                                                      some
                                                        (UpcrossingUp.mk
                                                          (upcrossingDecodeBHist omega)
                                                          (upcrossingDecodeBHist martingale)
                                                          (upcrossingDecodeBHist lower)
                                                          (upcrossingDecodeBHist upper)
                                                          (upcrossingDecodeBHist horizon)
                                                          (upcrossingDecodeBHist values)
                                                          (upcrossingDecodeBHist lowerLedger)
                                                          (upcrossingDecodeBHist upperLedger)
                                                          (upcrossingDecodeBHist transport)
                                                          (upcrossingDecodeBHist routes)
                                                          (upcrossingDecodeBHist provenance)
                                                          (upcrossingDecodeBHist nameCert))
                                                  | _ :: _ => none

private theorem upcrossing_round_trip :
    ∀ x : UpcrossingUp, upcrossingFromEventFlow (upcrossingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk omega martingale lower upper horizon values lowerLedger upperLedger transport routes
      provenance nameCert =>
      change
        some
          (UpcrossingUp.mk
            (upcrossingDecodeBHist (upcrossingEncodeBHist omega))
            (upcrossingDecodeBHist (upcrossingEncodeBHist martingale))
            (upcrossingDecodeBHist (upcrossingEncodeBHist lower))
            (upcrossingDecodeBHist (upcrossingEncodeBHist upper))
            (upcrossingDecodeBHist (upcrossingEncodeBHist horizon))
            (upcrossingDecodeBHist (upcrossingEncodeBHist values))
            (upcrossingDecodeBHist (upcrossingEncodeBHist lowerLedger))
            (upcrossingDecodeBHist (upcrossingEncodeBHist upperLedger))
            (upcrossingDecodeBHist (upcrossingEncodeBHist transport))
            (upcrossingDecodeBHist (upcrossingEncodeBHist routes))
            (upcrossingDecodeBHist (upcrossingEncodeBHist provenance))
            (upcrossingDecodeBHist (upcrossingEncodeBHist nameCert))) =
          some
            (UpcrossingUp.mk omega martingale lower upper horizon values lowerLedger
              upperLedger transport routes provenance nameCert)
      rw [upcrossingDecode_encode_bhist omega, upcrossingDecode_encode_bhist martingale,
        upcrossingDecode_encode_bhist lower, upcrossingDecode_encode_bhist upper,
        upcrossingDecode_encode_bhist horizon, upcrossingDecode_encode_bhist values,
        upcrossingDecode_encode_bhist lowerLedger, upcrossingDecode_encode_bhist upperLedger,
        upcrossingDecode_encode_bhist transport, upcrossingDecode_encode_bhist routes,
        upcrossingDecode_encode_bhist provenance, upcrossingDecode_encode_bhist nameCert]

private theorem upcrossingToEventFlow_injective {x y : UpcrossingUp} :
    upcrossingToEventFlow x = upcrossingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upcrossingFromEventFlow (upcrossingToEventFlow x) =
        upcrossingFromEventFlow (upcrossingToEventFlow y) :=
    congrArg upcrossingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (upcrossing_round_trip x).symm
      (Eq.trans hread (upcrossing_round_trip y)))

private theorem upcrossing_fields_faithful :
    ∀ x y : UpcrossingUp, upcrossingFields x = upcrossingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk omega₁ martingale₁ lower₁ upper₁ horizon₁ values₁ lowerLedger₁ upperLedger₁
      transport₁ routes₁ provenance₁ nameCert₁ =>
      cases y with
      | mk omega₂ martingale₂ lower₂ upper₂ horizon₂ values₂ lowerLedger₂ upperLedger₂
          transport₂ routes₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance upcrossingBHistCarrier : BHistCarrier UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upcrossingToEventFlow
  fromEventFlow := upcrossingFromEventFlow

instance upcrossingChapterTasteGate : ChapterTasteGate UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upcrossingFromEventFlow (upcrossingToEventFlow x) = some x
    exact upcrossing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upcrossingToEventFlow_injective heq)

instance upcrossingFieldFaithful : FieldFaithful UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := upcrossingFields
  field_faithful := upcrossing_fields_faithful

instance upcrossingNontrivial : Nontrivial UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpcrossingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpcrossingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UpcrossingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  upcrossingChapterTasteGate

theorem UpcrossingTasteGate_single_carrier_alignment :
    (∀ h : BHist, upcrossingDecodeBHist (upcrossingEncodeBHist h) = h) ∧
      (∀ x : UpcrossingUp, upcrossingFromEventFlow (upcrossingToEventFlow x) = some x) ∧
        (∀ x y : UpcrossingUp, upcrossingToEventFlow x = upcrossingToEventFlow y → x = y) ∧
          upcrossingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact upcrossingDecode_encode_bhist
  constructor
  · exact upcrossing_round_trip
  constructor
  · intro x y heq
    exact upcrossingToEventFlow_injective heq
  · rfl

end BEDC.Derived.UpcrossingUp
