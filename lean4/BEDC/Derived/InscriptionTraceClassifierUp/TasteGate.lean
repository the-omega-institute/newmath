import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionTraceClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionTraceClassifierUp : Type where
  | mk : (source name route check consumer ledger transport routes provenance nameCert : BHist) →
      InscriptionTraceClassifierUp
  deriving DecidableEq

def inscriptionTraceClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionTraceClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionTraceClassifierEncodeBHist h

def inscriptionTraceClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionTraceClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionTraceClassifierDecodeBHist tail)

private theorem inscriptionTraceClassifierDecode_encode_bhist :
    ∀ h : BHist,
      inscriptionTraceClassifierDecodeBHist (inscriptionTraceClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def inscriptionTraceClassifierToEventFlow : InscriptionTraceClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionTraceClassifierUp.mk source name route check consumer ledger transport routes
      provenance nameCert =>
      [[BMark.b0],
        inscriptionTraceClassifierEncodeBHist source,
        [BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist check,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionTraceClassifierEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        inscriptionTraceClassifierEncodeBHist nameCert]

def inscriptionTraceClassifierFromEventFlow : EventFlow → Option InscriptionTraceClassifierUp
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
              | name :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | check :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | consumer :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (InscriptionTraceClassifierUp.mk
                                                                                          (inscriptionTraceClassifierDecodeBHist source)
                                                                                          (inscriptionTraceClassifierDecodeBHist name)
                                                                                          (inscriptionTraceClassifierDecodeBHist route)
                                                                                          (inscriptionTraceClassifierDecodeBHist check)
                                                                                          (inscriptionTraceClassifierDecodeBHist consumer)
                                                                                          (inscriptionTraceClassifierDecodeBHist ledger)
                                                                                          (inscriptionTraceClassifierDecodeBHist transport)
                                                                                          (inscriptionTraceClassifierDecodeBHist routes)
                                                                                          (inscriptionTraceClassifierDecodeBHist provenance)
                                                                                          (inscriptionTraceClassifierDecodeBHist nameCert))
                                                                                  | _ :: _ => none

private theorem inscriptionTraceClassifier_round_trip :
    ∀ x : InscriptionTraceClassifierUp,
      inscriptionTraceClassifierFromEventFlow (inscriptionTraceClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source name route check consumer ledger transport routes provenance nameCert =>
      change
        some
          (InscriptionTraceClassifierUp.mk
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist source))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist name))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist route))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist check))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist consumer))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist ledger))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist transport))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist routes))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist provenance))
            (inscriptionTraceClassifierDecodeBHist
              (inscriptionTraceClassifierEncodeBHist nameCert))) =
          some
            (InscriptionTraceClassifierUp.mk source name route check consumer ledger transport
              routes provenance nameCert)
      rw [inscriptionTraceClassifierDecode_encode_bhist source,
        inscriptionTraceClassifierDecode_encode_bhist name,
        inscriptionTraceClassifierDecode_encode_bhist route,
        inscriptionTraceClassifierDecode_encode_bhist check,
        inscriptionTraceClassifierDecode_encode_bhist consumer,
        inscriptionTraceClassifierDecode_encode_bhist ledger,
        inscriptionTraceClassifierDecode_encode_bhist transport,
        inscriptionTraceClassifierDecode_encode_bhist routes,
        inscriptionTraceClassifierDecode_encode_bhist provenance,
        inscriptionTraceClassifierDecode_encode_bhist nameCert]

private theorem inscriptionTraceClassifierToEventFlow_injective
    {x y : InscriptionTraceClassifierUp} :
    inscriptionTraceClassifierToEventFlow x = inscriptionTraceClassifierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionTraceClassifierFromEventFlow (inscriptionTraceClassifierToEventFlow x) =
        inscriptionTraceClassifierFromEventFlow (inscriptionTraceClassifierToEventFlow y) :=
    congrArg inscriptionTraceClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionTraceClassifier_round_trip x).symm
      (Eq.trans hread (inscriptionTraceClassifier_round_trip y)))

instance inscriptionTraceClassifierBHistCarrier :
    BHistCarrier InscriptionTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionTraceClassifierToEventFlow
  fromEventFlow := inscriptionTraceClassifierFromEventFlow

instance inscriptionTraceClassifierChapterTasteGate :
    ChapterTasteGate InscriptionTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inscriptionTraceClassifierFromEventFlow (inscriptionTraceClassifierToEventFlow x) =
        some x
    exact inscriptionTraceClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionTraceClassifierToEventFlow_injective heq)

def inscriptionTraceClassifierFields (x : InscriptionTraceClassifierUp) : List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  match x with
  | InscriptionTraceClassifierUp.mk source name route check consumer ledger transport routes
      provenance nameCert =>
      [source, name, route, check, consumer, ledger, transport, routes, provenance, nameCert]

private theorem inscriptionTraceClassifierFields_faithful :
    ∀ x y : InscriptionTraceClassifierUp,
      inscriptionTraceClassifierFields x = inscriptionTraceClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ name₁ route₁ check₁ consumer₁ ledger₁ transport₁ routes₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk source₂ name₂ route₂ check₂ consumer₂ ledger₂ transport₂ routes₂ provenance₂
          nameCert₂ =>
          simp only [inscriptionTraceClassifierFields] at h
          injection h with hSource hRest₁
          injection hRest₁ with hName hRest₂
          injection hRest₂ with hRoute hRest₃
          injection hRest₃ with hCheck hRest₄
          injection hRest₄ with hConsumer hRest₅
          injection hRest₅ with hLedger hRest₆
          injection hRest₆ with hTransport hRest₇
          injection hRest₇ with hRoutes hRest₈
          injection hRest₈ with hProvenance hRest₉
          injection hRest₉ with hNameCert _
          subst hSource
          subst hName
          subst hRoute
          subst hCheck
          subst hConsumer
          subst hLedger
          subst hTransport
          subst hRoutes
          subst hProvenance
          subst hNameCert
          rfl

instance inscriptionTraceClassifierFieldFaithful :
    FieldFaithful InscriptionTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inscriptionTraceClassifierFields
  field_faithful := inscriptionTraceClassifierFields_faithful

instance inscriptionTraceClassifierNontrivial :
    Nontrivial InscriptionTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InscriptionTraceClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscriptionTraceClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InscriptionTraceClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inscriptionTraceClassifierChapterTasteGate

theorem InscriptionTraceClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inscriptionTraceClassifierDecodeBHist (inscriptionTraceClassifierEncodeBHist h) = h) ∧
      (∀ x : InscriptionTraceClassifierUp,
        inscriptionTraceClassifierFromEventFlow (inscriptionTraceClassifierToEventFlow x) =
          some x) ∧
        (∀ x y : InscriptionTraceClassifierUp,
          inscriptionTraceClassifierToEventFlow x =
            inscriptionTraceClassifierToEventFlow y → x = y) ∧
          inscriptionTraceClassifierEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : InscriptionTraceClassifierUp,
              inscriptionTraceClassifierFields x = inscriptionTraceClassifierFields y → x = y) ∧
              (∃ x y : InscriptionTraceClassifierUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionTraceClassifierDecode_encode_bhist
  · constructor
    · exact inscriptionTraceClassifier_round_trip
    · constructor
      · intro x y heq
        exact inscriptionTraceClassifierToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact inscriptionTraceClassifierFields_faithful
          · exact
              ⟨InscriptionTraceClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                InscriptionTraceClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

namespace TasteGate

theorem InscriptionTraceClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inscriptionTraceClassifierDecodeBHist (inscriptionTraceClassifierEncodeBHist h) = h) ∧
      (∀ x : InscriptionTraceClassifierUp,
        inscriptionTraceClassifierFromEventFlow (inscriptionTraceClassifierToEventFlow x) =
          some x) ∧
        (∀ x y : InscriptionTraceClassifierUp,
          inscriptionTraceClassifierToEventFlow x =
            inscriptionTraceClassifierToEventFlow y → x = y) ∧
          inscriptionTraceClassifierEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : InscriptionTraceClassifierUp,
              inscriptionTraceClassifierFields x = inscriptionTraceClassifierFields y → x = y) ∧
              (∃ x y : InscriptionTraceClassifierUp, x ≠ y) :=
  InscriptionTraceClassifierUp.InscriptionTraceClassifierTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.InscriptionTraceClassifierUp
