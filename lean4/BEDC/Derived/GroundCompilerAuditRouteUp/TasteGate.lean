import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerAuditRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerAuditRouteUp : Type where
  | mk (E M B Q T R V H C P N : BHist) : GroundCompilerAuditRouteUp
  deriving DecidableEq

def groundCompilerAuditRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerAuditRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerAuditRouteEncodeBHist h

def groundCompilerAuditRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerAuditRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerAuditRouteDecodeBHist tail)

private theorem groundCompilerAuditRoute_decode_encode_bhist :
    ∀ h : BHist,
      groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def groundCompilerAuditRouteFields : GroundCompilerAuditRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerAuditRouteUp.mk E M B Q T R V H C P N => [E, M, B, Q, T, R, V, H, C, P, N]

def groundCompilerAuditRouteToEventFlow : GroundCompilerAuditRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (groundCompilerAuditRouteFields x).map groundCompilerAuditRouteEncodeBHist

def groundCompilerAuditRouteFromEventFlow : EventFlow → Option GroundCompilerAuditRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | V :: rest6 =>
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
                                                    (GroundCompilerAuditRouteUp.mk
                                                      (groundCompilerAuditRouteDecodeBHist E)
                                                      (groundCompilerAuditRouteDecodeBHist M)
                                                      (groundCompilerAuditRouteDecodeBHist B)
                                                      (groundCompilerAuditRouteDecodeBHist Q)
                                                      (groundCompilerAuditRouteDecodeBHist T)
                                                      (groundCompilerAuditRouteDecodeBHist R)
                                                      (groundCompilerAuditRouteDecodeBHist V)
                                                      (groundCompilerAuditRouteDecodeBHist H)
                                                      (groundCompilerAuditRouteDecodeBHist C)
                                                      (groundCompilerAuditRouteDecodeBHist P)
                                                      (groundCompilerAuditRouteDecodeBHist N))
                                              | _ :: _ => none

private theorem groundCompilerAuditRoute_round_trip :
    ∀ x : GroundCompilerAuditRouteUp,
      groundCompilerAuditRouteFromEventFlow (groundCompilerAuditRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E M B Q T R V H C P N =>
      change
        some
          (GroundCompilerAuditRouteUp.mk
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist E))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist M))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist B))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist Q))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist T))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist R))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist V))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist H))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist C))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist P))
            (groundCompilerAuditRouteDecodeBHist (groundCompilerAuditRouteEncodeBHist N))) =
          some (GroundCompilerAuditRouteUp.mk E M B Q T R V H C P N)
      rw [groundCompilerAuditRoute_decode_encode_bhist E,
        groundCompilerAuditRoute_decode_encode_bhist M,
        groundCompilerAuditRoute_decode_encode_bhist B,
        groundCompilerAuditRoute_decode_encode_bhist Q,
        groundCompilerAuditRoute_decode_encode_bhist T,
        groundCompilerAuditRoute_decode_encode_bhist R,
        groundCompilerAuditRoute_decode_encode_bhist V,
        groundCompilerAuditRoute_decode_encode_bhist H,
        groundCompilerAuditRoute_decode_encode_bhist C,
        groundCompilerAuditRoute_decode_encode_bhist P,
        groundCompilerAuditRoute_decode_encode_bhist N]

private theorem groundCompilerAuditRouteToEventFlow_injective
    {x y : GroundCompilerAuditRouteUp} :
    groundCompilerAuditRouteToEventFlow x = groundCompilerAuditRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerAuditRouteFromEventFlow (groundCompilerAuditRouteToEventFlow x) =
        groundCompilerAuditRouteFromEventFlow (groundCompilerAuditRouteToEventFlow y) :=
    congrArg groundCompilerAuditRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerAuditRoute_round_trip x).symm
      (Eq.trans hread (groundCompilerAuditRoute_round_trip y)))

private theorem groundCompilerAuditRoute_field_faithful :
    ∀ x y : GroundCompilerAuditRouteUp,
      groundCompilerAuditRouteFields x = groundCompilerAuditRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ M₁ B₁ Q₁ T₁ R₁ V₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ M₂ B₂ Q₂ T₂ R₂ V₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hE tail0
          injection tail0 with hM tail1
          injection tail1 with hB tail2
          injection tail2 with hQ tail3
          injection tail3 with hT tail4
          injection tail4 with hR tail5
          injection tail5 with hV tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hE
          subst hM
          subst hB
          subst hQ
          subst hT
          subst hR
          subst hV
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance groundCompilerAuditRouteBHistCarrier : BHistCarrier GroundCompilerAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerAuditRouteToEventFlow
  fromEventFlow := groundCompilerAuditRouteFromEventFlow

instance groundCompilerAuditRouteChapterTasteGate :
    ChapterTasteGate GroundCompilerAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change groundCompilerAuditRouteFromEventFlow (groundCompilerAuditRouteToEventFlow x) = some x
    exact groundCompilerAuditRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerAuditRouteToEventFlow_injective heq)

instance groundCompilerAuditRouteFieldFaithful :
    FieldFaithful GroundCompilerAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := groundCompilerAuditRouteFields
  field_faithful := groundCompilerAuditRoute_field_faithful

instance groundCompilerAuditRouteNontrivial : Nontrivial GroundCompilerAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GroundCompilerAuditRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GroundCompilerAuditRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GroundCompilerAuditRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  groundCompilerAuditRouteChapterTasteGate

theorem GroundCompilerAuditRouteTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GroundCompilerAuditRouteUp) ∧
      (∀ x : GroundCompilerAuditRouteUp,
        ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
        ∃ x : GroundCompilerAuditRouteUp,
          x =
            GroundCompilerAuditRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨groundCompilerAuditRouteChapterTasteGate⟩
  · constructor
    · intro x
      exact ⟨groundCompilerAuditRouteToEventFlow x, ChapterTasteGate.round_trip x⟩
    · exact
        ⟨GroundCompilerAuditRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty,
          rfl⟩

end BEDC.Derived.GroundCompilerAuditRouteUp
