import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TraditionComparisonBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TraditionComparisonBoundaryUp : Type where
  | mk :
      (source landing rejectedSurplus distinction transport replay provenance localName :
        BHist) →
      TraditionComparisonBoundaryUp
  deriving DecidableEq

def traditionComparisonBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: traditionComparisonBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: traditionComparisonBoundaryEncodeBHist h

def traditionComparisonBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (traditionComparisonBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (traditionComparisonBoundaryDecodeBHist tail)

private theorem traditionComparisonBoundary_decode_encode_bhist :
    ∀ h : BHist,
      traditionComparisonBoundaryDecodeBHist (traditionComparisonBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def traditionComparisonBoundaryFields : TraditionComparisonBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TraditionComparisonBoundaryUp.mk source landing rejectedSurplus distinction transport
      replay provenance localName =>
      [source, landing, rejectedSurplus, distinction, transport, replay, provenance,
        localName]

def traditionComparisonBoundaryToEventFlow : TraditionComparisonBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map traditionComparisonBoundaryEncodeBHist (traditionComparisonBoundaryFields x)

def traditionComparisonBoundaryFromEventFlow :
    EventFlow → Option TraditionComparisonBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | landing :: rest1 =>
          match rest1 with
          | [] => none
          | rejectedSurplus :: rest2 =>
              match rest2 with
              | [] => none
              | distinction :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | replay :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (TraditionComparisonBoundaryUp.mk
                                          (traditionComparisonBoundaryDecodeBHist source)
                                          (traditionComparisonBoundaryDecodeBHist landing)
                                          (traditionComparisonBoundaryDecodeBHist
                                            rejectedSurplus)
                                          (traditionComparisonBoundaryDecodeBHist distinction)
                                          (traditionComparisonBoundaryDecodeBHist transport)
                                          (traditionComparisonBoundaryDecodeBHist replay)
                                          (traditionComparisonBoundaryDecodeBHist provenance)
                                          (traditionComparisonBoundaryDecodeBHist localName))
                                  | _ :: _ => none

private theorem traditionComparisonBoundary_round_trip :
    ∀ x : TraditionComparisonBoundaryUp,
      traditionComparisonBoundaryFromEventFlow
        (traditionComparisonBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source landing rejectedSurplus distinction transport replay provenance localName =>
      change
        some
          (TraditionComparisonBoundaryUp.mk
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist source))
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist landing))
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist rejectedSurplus))
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist distinction))
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist transport))
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist replay))
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist provenance))
            (traditionComparisonBoundaryDecodeBHist
              (traditionComparisonBoundaryEncodeBHist localName))) =
          some
            (TraditionComparisonBoundaryUp.mk source landing rejectedSurplus distinction
              transport replay provenance localName)
      rw [traditionComparisonBoundary_decode_encode_bhist source,
        traditionComparisonBoundary_decode_encode_bhist landing,
        traditionComparisonBoundary_decode_encode_bhist rejectedSurplus,
        traditionComparisonBoundary_decode_encode_bhist distinction,
        traditionComparisonBoundary_decode_encode_bhist transport,
        traditionComparisonBoundary_decode_encode_bhist replay,
        traditionComparisonBoundary_decode_encode_bhist provenance,
        traditionComparisonBoundary_decode_encode_bhist localName]

private theorem traditionComparisonBoundaryToEventFlow_injective
    {x y : TraditionComparisonBoundaryUp} :
    traditionComparisonBoundaryToEventFlow x =
      traditionComparisonBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      traditionComparisonBoundaryFromEventFlow (traditionComparisonBoundaryToEventFlow x) =
        traditionComparisonBoundaryFromEventFlow (traditionComparisonBoundaryToEventFlow y) :=
    congrArg traditionComparisonBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (traditionComparisonBoundary_round_trip x).symm
      (Eq.trans hread (traditionComparisonBoundary_round_trip y)))

private theorem traditionComparisonBoundary_field_faithful :
    ∀ x y : TraditionComparisonBoundaryUp,
      traditionComparisonBoundaryFields x = traditionComparisonBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ landing₁ rejectedSurplus₁ distinction₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk source₂ landing₂ rejectedSurplus₂ distinction₂ transport₂ replay₂ provenance₂
          localName₂ =>
          cases hfields
          rfl

instance traditionComparisonBoundaryBHistCarrier :
    BHistCarrier TraditionComparisonBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := traditionComparisonBoundaryToEventFlow
  fromEventFlow := traditionComparisonBoundaryFromEventFlow

instance traditionComparisonBoundaryChapterTasteGate :
    ChapterTasteGate TraditionComparisonBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      traditionComparisonBoundaryFromEventFlow
        (traditionComparisonBoundaryToEventFlow x) = some x
    exact traditionComparisonBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (traditionComparisonBoundaryToEventFlow_injective heq)

instance traditionComparisonBoundaryFieldFaithful :
    FieldFaithful TraditionComparisonBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := traditionComparisonBoundaryFields
  field_faithful := traditionComparisonBoundary_field_faithful

instance traditionComparisonBoundaryNontrivial :
    Nontrivial TraditionComparisonBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TraditionComparisonBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TraditionComparisonBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TraditionComparisonBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  traditionComparisonBoundaryChapterTasteGate

theorem TraditionComparisonBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        traditionComparisonBoundaryDecodeBHist
          (traditionComparisonBoundaryEncodeBHist h) = h) ∧
      (∀ x : TraditionComparisonBoundaryUp,
        traditionComparisonBoundaryFromEventFlow
          (traditionComparisonBoundaryToEventFlow x) = some x) ∧
        (∀ x y : TraditionComparisonBoundaryUp,
          traditionComparisonBoundaryToEventFlow x =
            traditionComparisonBoundaryToEventFlow y -> x = y) ∧
          traditionComparisonBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : TraditionComparisonBoundaryUp,
              traditionComparisonBoundaryFields x =
                traditionComparisonBoundaryFields y -> x = y) ∧
              (∃ x y : TraditionComparisonBoundaryUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact traditionComparisonBoundary_decode_encode_bhist
  · constructor
    · exact traditionComparisonBoundary_round_trip
    · constructor
      · intro x y heq
        exact traditionComparisonBoundaryToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact traditionComparisonBoundary_field_faithful
          · exact
              ⟨TraditionComparisonBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                TraditionComparisonBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.TraditionComparisonBoundaryUp
