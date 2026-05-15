import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TarskiTruthRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TarskiTruthRefusalUp : Type where
  | mk :
      (sentenceCode query refusal diagonal ledger transport route provenance name : BHist) →
      TarskiTruthRefusalUp

def tarskiTruthRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tarskiTruthRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tarskiTruthRefusalEncodeBHist h

def tarskiTruthRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tarskiTruthRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tarskiTruthRefusalDecodeBHist tail)

private theorem tarskiTruthRefusal_decode_encode_bhist :
    ∀ h : BHist,
      tarskiTruthRefusalDecodeBHist (tarskiTruthRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tarskiTruthRefusalFields : TarskiTruthRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TarskiTruthRefusalUp.mk sentenceCode query refusal diagonal ledger transport route
      provenance name =>
      [sentenceCode, query, refusal, diagonal, ledger, transport, route, provenance, name]

def tarskiTruthRefusalToEventFlow : TarskiTruthRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tarskiTruthRefusalFields x).map tarskiTruthRefusalEncodeBHist

def tarskiTruthRefusalFromEventFlow : EventFlow → Option TarskiTruthRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sentenceCode :: rest0 =>
      match rest0 with
      | [] => none
      | query :: rest1 =>
          match rest1 with
          | [] => none
          | refusal :: rest2 =>
              match rest2 with
              | [] => none
              | diagonal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | ledger :: rest4 =>
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
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (TarskiTruthRefusalUp.mk
                                              (tarskiTruthRefusalDecodeBHist sentenceCode)
                                              (tarskiTruthRefusalDecodeBHist query)
                                              (tarskiTruthRefusalDecodeBHist refusal)
                                              (tarskiTruthRefusalDecodeBHist diagonal)
                                              (tarskiTruthRefusalDecodeBHist ledger)
                                              (tarskiTruthRefusalDecodeBHist transport)
                                              (tarskiTruthRefusalDecodeBHist route)
                                              (tarskiTruthRefusalDecodeBHist provenance)
                                              (tarskiTruthRefusalDecodeBHist name))
                                      | _ :: _ => none

private theorem tarskiTruthRefusal_round_trip :
    ∀ x : TarskiTruthRefusalUp,
      tarskiTruthRefusalFromEventFlow (tarskiTruthRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sentenceCode query refusal diagonal ledger transport route provenance name =>
      change
        some
          (TarskiTruthRefusalUp.mk
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist sentenceCode))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist query))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist refusal))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist diagonal))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist ledger))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist transport))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist route))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist provenance))
            (tarskiTruthRefusalDecodeBHist
              (tarskiTruthRefusalEncodeBHist name))) =
          some
            (TarskiTruthRefusalUp.mk sentenceCode query refusal diagonal ledger transport route
              provenance name)
      rw [tarskiTruthRefusal_decode_encode_bhist sentenceCode,
        tarskiTruthRefusal_decode_encode_bhist query,
        tarskiTruthRefusal_decode_encode_bhist refusal,
        tarskiTruthRefusal_decode_encode_bhist diagonal,
        tarskiTruthRefusal_decode_encode_bhist ledger,
        tarskiTruthRefusal_decode_encode_bhist transport,
        tarskiTruthRefusal_decode_encode_bhist route,
        tarskiTruthRefusal_decode_encode_bhist provenance,
        tarskiTruthRefusal_decode_encode_bhist name]

private theorem tarskiTruthRefusalToEventFlow_injective {x y : TarskiTruthRefusalUp} :
    tarskiTruthRefusalToEventFlow x = tarskiTruthRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tarskiTruthRefusalFromEventFlow (tarskiTruthRefusalToEventFlow x) =
        tarskiTruthRefusalFromEventFlow (tarskiTruthRefusalToEventFlow y) :=
    congrArg tarskiTruthRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tarskiTruthRefusal_round_trip x).symm
      (Eq.trans hread (tarskiTruthRefusal_round_trip y)))

private theorem tarskiTruthRefusal_fields_faithful :
    ∀ x y : TarskiTruthRefusalUp,
      tarskiTruthRefusalFields x = tarskiTruthRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sentenceCode₁ query₁ refusal₁ diagonal₁ ledger₁ transport₁ route₁ provenance₁
      name₁ =>
      cases y with
      | mk sentenceCode₂ query₂ refusal₂ diagonal₂ ledger₂ transport₂ route₂ provenance₂
          name₂ =>
          cases hfields
          rfl

instance tarskiTruthRefusalBHistCarrier :
    BHistCarrier TarskiTruthRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tarskiTruthRefusalToEventFlow
  fromEventFlow := tarskiTruthRefusalFromEventFlow

instance tarskiTruthRefusalChapterTasteGate :
    ChapterTasteGate TarskiTruthRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tarskiTruthRefusalFromEventFlow (tarskiTruthRefusalToEventFlow x) = some x
    exact tarskiTruthRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tarskiTruthRefusalToEventFlow_injective heq)

instance tarskiTruthRefusalFieldFaithful :
    FieldFaithful TarskiTruthRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tarskiTruthRefusalFields
  field_faithful := tarskiTruthRefusal_fields_faithful

instance tarskiTruthRefusalNontrivial :
    Nontrivial TarskiTruthRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TarskiTruthRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TarskiTruthRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TarskiTruthRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tarskiTruthRefusalChapterTasteGate

theorem TarskiTruthRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist, tarskiTruthRefusalDecodeBHist (tarskiTruthRefusalEncodeBHist h) = h) ∧
      (∀ x : TarskiTruthRefusalUp,
        tarskiTruthRefusalFromEventFlow (tarskiTruthRefusalToEventFlow x) = some x) ∧
        (∀ x y : TarskiTruthRefusalUp,
          tarskiTruthRefusalToEventFlow x = tarskiTruthRefusalToEventFlow y → x = y) ∧
          tarskiTruthRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨tarskiTruthRefusal_decode_encode_bhist, tarskiTruthRefusal_round_trip,
      fun x y heq => tarskiTruthRefusalToEventFlow_injective heq, rfl⟩

end BEDC.Derived.TarskiTruthRefusalUp
