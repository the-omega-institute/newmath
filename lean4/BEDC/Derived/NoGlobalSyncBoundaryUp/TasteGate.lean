import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoGlobalSyncBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NoGlobalSyncBoundaryUp : Type where
  | mk (histories locality refusal transport routes provenance name : BHist) :
      NoGlobalSyncBoundaryUp
  deriving DecidableEq

def noGlobalSyncBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noGlobalSyncBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noGlobalSyncBoundaryEncodeBHist h

def noGlobalSyncBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noGlobalSyncBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noGlobalSyncBoundaryDecodeBHist tail)

private theorem noGlobalSyncBoundary_decode_encode_bhist :
    ∀ h : BHist, noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def noGlobalSyncBoundaryToEventFlow : NoGlobalSyncBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NoGlobalSyncBoundaryUp.mk histories locality refusal transport routes provenance name =>
      [[BMark.b0],
        noGlobalSyncBoundaryEncodeBHist histories,
        [BMark.b1, BMark.b0],
        noGlobalSyncBoundaryEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b0],
        noGlobalSyncBoundaryEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSyncBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSyncBoundaryEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSyncBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSyncBoundaryEncodeBHist name]

def noGlobalSyncBoundaryFromEventFlow : EventFlow → Option NoGlobalSyncBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | histories :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | locality :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | routes :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (NoGlobalSyncBoundaryUp.mk
                                                                  (noGlobalSyncBoundaryDecodeBHist
                                                                    histories)
                                                                  (noGlobalSyncBoundaryDecodeBHist
                                                                    locality)
                                                                  (noGlobalSyncBoundaryDecodeBHist
                                                                    refusal)
                                                                  (noGlobalSyncBoundaryDecodeBHist
                                                                    transport)
                                                                  (noGlobalSyncBoundaryDecodeBHist
                                                                    routes)
                                                                  (noGlobalSyncBoundaryDecodeBHist
                                                                    provenance)
                                                                  (noGlobalSyncBoundaryDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem noGlobalSyncBoundary_round_trip :
    ∀ x : NoGlobalSyncBoundaryUp,
      noGlobalSyncBoundaryFromEventFlow (noGlobalSyncBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk histories locality refusal transport routes provenance name =>
      change
        some
          (NoGlobalSyncBoundaryUp.mk
            (noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist histories))
            (noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist locality))
            (noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist refusal))
            (noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist transport))
            (noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist routes))
            (noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist provenance))
            (noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist name))) =
          some
            (NoGlobalSyncBoundaryUp.mk histories locality refusal transport routes provenance name)
      rw [noGlobalSyncBoundary_decode_encode_bhist histories,
        noGlobalSyncBoundary_decode_encode_bhist locality,
        noGlobalSyncBoundary_decode_encode_bhist refusal,
        noGlobalSyncBoundary_decode_encode_bhist transport,
        noGlobalSyncBoundary_decode_encode_bhist routes,
        noGlobalSyncBoundary_decode_encode_bhist provenance,
        noGlobalSyncBoundary_decode_encode_bhist name]

private theorem noGlobalSyncBoundaryToEventFlow_injective {x y : NoGlobalSyncBoundaryUp} :
    noGlobalSyncBoundaryToEventFlow x = noGlobalSyncBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noGlobalSyncBoundaryFromEventFlow (noGlobalSyncBoundaryToEventFlow x) =
        noGlobalSyncBoundaryFromEventFlow (noGlobalSyncBoundaryToEventFlow y) :=
    congrArg noGlobalSyncBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (noGlobalSyncBoundary_round_trip x).symm
      (Eq.trans hread (noGlobalSyncBoundary_round_trip y)))

instance noGlobalSyncBoundaryBHistCarrier : BHistCarrier NoGlobalSyncBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noGlobalSyncBoundaryToEventFlow
  fromEventFlow := noGlobalSyncBoundaryFromEventFlow

instance noGlobalSyncBoundaryChapterTasteGate : ChapterTasteGate NoGlobalSyncBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change noGlobalSyncBoundaryFromEventFlow (noGlobalSyncBoundaryToEventFlow x) = some x
    exact noGlobalSyncBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (noGlobalSyncBoundaryToEventFlow_injective heq)

instance noGlobalSyncBoundaryFieldFaithful : FieldFaithful NoGlobalSyncBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | NoGlobalSyncBoundaryUp.mk histories locality refusal transport routes provenance name =>
        [histories, locality, refusal, transport, routes, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk histories₁ locality₁ refusal₁ transport₁ routes₁ provenance₁ name₁ =>
        cases y with
        | mk histories₂ locality₂ refusal₂ transport₂ routes₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance noGlobalSyncBoundaryNontrivial : Nontrivial NoGlobalSyncBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NoGlobalSyncBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      NoGlobalSyncBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NoGlobalSyncBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  noGlobalSyncBoundaryChapterTasteGate

theorem NoGlobalSyncBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, noGlobalSyncBoundaryDecodeBHist (noGlobalSyncBoundaryEncodeBHist h) = h) ∧
      (∀ x : NoGlobalSyncBoundaryUp,
        noGlobalSyncBoundaryFromEventFlow (noGlobalSyncBoundaryToEventFlow x) = some x) ∧
        (∀ x y : NoGlobalSyncBoundaryUp,
          noGlobalSyncBoundaryToEventFlow x = noGlobalSyncBoundaryToEventFlow y → x = y) ∧
          noGlobalSyncBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact noGlobalSyncBoundary_decode_encode_bhist
  · constructor
    · exact noGlobalSyncBoundary_round_trip
    · constructor
      · intro x y heq
        exact noGlobalSyncBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.NoGlobalSyncBoundaryUp
