import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyInverseBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyInverseBudgetUp : Type where
  | mk :
      (source apartness modulus window dyadicReadback regularReadback realSeal transport routes
        provenance nameCert : BHist) →
      CauchyInverseBudgetUp
  deriving DecidableEq

def cauchyInverseBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyInverseBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyInverseBudgetEncodeBHist h

def cauchyInverseBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyInverseBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyInverseBudgetDecodeBHist tail)

private theorem cauchyInverseBudgetDecode_encode_bhist :
    ∀ h : BHist, cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyInverseBudgetToEventFlow : CauchyInverseBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyInverseBudgetUp.mk source apartness modulus window dyadicReadback regularReadback
      realSeal transport routes provenance nameCert =>
      [[BMark.b0],
        cauchyInverseBudgetEncodeBHist source,
        [BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist apartness,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist dyadicReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist regularReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyInverseBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyInverseBudgetEncodeBHist nameCert]

def cauchyInverseBudgetFromEventFlow : EventFlow → Option CauchyInverseBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | apartness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | modulus :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | window :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadicReadback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | regularReadback :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | realSeal :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CauchyInverseBudgetUp.mk
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    source)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    apartness)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    modulus)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    window)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    dyadicReadback)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    regularReadback)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    realSeal)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    transport)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    routes)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    provenance)
                                                                                                  (cauchyInverseBudgetDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ => none

private theorem cauchyInverseBudget_round_trip :
    ∀ x : CauchyInverseBudgetUp,
      cauchyInverseBudgetFromEventFlow (cauchyInverseBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source apartness modulus window dyadicReadback regularReadback realSeal transport routes
      provenance nameCert =>
      change
        some
          (CauchyInverseBudgetUp.mk
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist source))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist apartness))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist modulus))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist window))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist dyadicReadback))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist regularReadback))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist realSeal))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist transport))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist routes))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist provenance))
            (cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist nameCert))) =
          some
            (CauchyInverseBudgetUp.mk source apartness modulus window dyadicReadback
              regularReadback realSeal transport routes provenance nameCert)
      rw [cauchyInverseBudgetDecode_encode_bhist source,
        cauchyInverseBudgetDecode_encode_bhist apartness,
        cauchyInverseBudgetDecode_encode_bhist modulus,
        cauchyInverseBudgetDecode_encode_bhist window,
        cauchyInverseBudgetDecode_encode_bhist dyadicReadback,
        cauchyInverseBudgetDecode_encode_bhist regularReadback,
        cauchyInverseBudgetDecode_encode_bhist realSeal,
        cauchyInverseBudgetDecode_encode_bhist transport,
        cauchyInverseBudgetDecode_encode_bhist routes,
        cauchyInverseBudgetDecode_encode_bhist provenance,
        cauchyInverseBudgetDecode_encode_bhist nameCert]

private theorem cauchyInverseBudgetToEventFlow_injective {x y : CauchyInverseBudgetUp} :
    cauchyInverseBudgetToEventFlow x = cauchyInverseBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyInverseBudgetFromEventFlow (cauchyInverseBudgetToEventFlow x) =
        cauchyInverseBudgetFromEventFlow (cauchyInverseBudgetToEventFlow y) :=
    congrArg cauchyInverseBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyInverseBudget_round_trip x).symm
      (Eq.trans hread (cauchyInverseBudget_round_trip y)))

instance cauchyInverseBudgetBHistCarrier : BHistCarrier CauchyInverseBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyInverseBudgetToEventFlow
  fromEventFlow := cauchyInverseBudgetFromEventFlow

instance cauchyInverseBudgetChapterTasteGate : ChapterTasteGate CauchyInverseBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyInverseBudgetFromEventFlow (cauchyInverseBudgetToEventFlow x) = some x
    exact cauchyInverseBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyInverseBudgetToEventFlow_injective heq)

instance cauchyInverseBudgetFieldFaithful : FieldFaithful CauchyInverseBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CauchyInverseBudgetUp.mk source apartness modulus window dyadicReadback regularReadback
        realSeal transport routes provenance nameCert =>
        [source, apartness, modulus, window, dyadicReadback, regularReadback, realSeal,
          transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ apartness₁ modulus₁ window₁ dyadicReadback₁ regularReadback₁ realSeal₁
        transport₁ routes₁ provenance₁ nameCert₁ =>
        cases y with
        | mk source₂ apartness₂ modulus₂ window₂ dyadicReadback₂ regularReadback₂ realSeal₂
            transport₂ routes₂ provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

theorem CauchyInverseBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyInverseBudgetDecodeBHist (cauchyInverseBudgetEncodeBHist h) = h) ∧
      (∀ x : CauchyInverseBudgetUp,
        cauchyInverseBudgetFromEventFlow (cauchyInverseBudgetToEventFlow x) = some x) ∧
        (∀ x y : CauchyInverseBudgetUp,
          cauchyInverseBudgetToEventFlow x = cauchyInverseBudgetToEventFlow y → x = y) ∧
          cauchyInverseBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyInverseBudgetDecode_encode_bhist
  · constructor
    · exact cauchyInverseBudget_round_trip
    · constructor
      · intro x y heq
        exact cauchyInverseBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyInverseBudgetUp
