import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplyAuditRouteUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplyAuditRouteUp : Type where
  | mk (B W G L H P N : BHist) : ExternalSupplyAuditRouteUp
  deriving DecidableEq

def externalSupplyAuditRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplyAuditRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplyAuditRouteEncodeBHist h

def externalSupplyAuditRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplyAuditRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplyAuditRouteDecodeBHist tail)

private theorem externalSupplyAuditRouteDecodeEncodeBHist :
    ∀ h : BHist,
      externalSupplyAuditRouteDecodeBHist
        (externalSupplyAuditRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def externalSupplyAuditRouteFields : ExternalSupplyAuditRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplyAuditRouteUp.mk B W G L H P N => [B, W, G, L, H, P, N]

def externalSupplyAuditRouteToEventFlow :
    ExternalSupplyAuditRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (externalSupplyAuditRouteFields x).map externalSupplyAuditRouteEncodeBHist

def externalSupplyAuditRouteFromEventFlow :
    EventFlow → Option ExternalSupplyAuditRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | G :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | P :: rest5 =>
                          match rest5 with
                          | [] => none
                          | N :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (ExternalSupplyAuditRouteUp.mk
                                      (externalSupplyAuditRouteDecodeBHist B)
                                      (externalSupplyAuditRouteDecodeBHist W)
                                      (externalSupplyAuditRouteDecodeBHist G)
                                      (externalSupplyAuditRouteDecodeBHist L)
                                      (externalSupplyAuditRouteDecodeBHist H)
                                      (externalSupplyAuditRouteDecodeBHist P)
                                      (externalSupplyAuditRouteDecodeBHist N))
                              | _ :: _ => none

private theorem externalSupplyAuditRouteRoundTrip :
    ∀ x : ExternalSupplyAuditRouteUp,
      externalSupplyAuditRouteFromEventFlow
        (externalSupplyAuditRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B W G L H P N =>
      change
        some
          (ExternalSupplyAuditRouteUp.mk
            (externalSupplyAuditRouteDecodeBHist
              (externalSupplyAuditRouteEncodeBHist B))
            (externalSupplyAuditRouteDecodeBHist
              (externalSupplyAuditRouteEncodeBHist W))
            (externalSupplyAuditRouteDecodeBHist
              (externalSupplyAuditRouteEncodeBHist G))
            (externalSupplyAuditRouteDecodeBHist
              (externalSupplyAuditRouteEncodeBHist L))
            (externalSupplyAuditRouteDecodeBHist
              (externalSupplyAuditRouteEncodeBHist H))
            (externalSupplyAuditRouteDecodeBHist
              (externalSupplyAuditRouteEncodeBHist P))
            (externalSupplyAuditRouteDecodeBHist
              (externalSupplyAuditRouteEncodeBHist N))) =
          some (ExternalSupplyAuditRouteUp.mk B W G L H P N)
      rw [externalSupplyAuditRouteDecodeEncodeBHist B,
        externalSupplyAuditRouteDecodeEncodeBHist W,
        externalSupplyAuditRouteDecodeEncodeBHist G,
        externalSupplyAuditRouteDecodeEncodeBHist L,
        externalSupplyAuditRouteDecodeEncodeBHist H,
        externalSupplyAuditRouteDecodeEncodeBHist P,
        externalSupplyAuditRouteDecodeEncodeBHist N]

private theorem externalSupplyAuditRouteToEventFlow_injective
    {x y : ExternalSupplyAuditRouteUp} :
    externalSupplyAuditRouteToEventFlow x =
      externalSupplyAuditRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplyAuditRouteFromEventFlow
          (externalSupplyAuditRouteToEventFlow x) =
        externalSupplyAuditRouteFromEventFlow
          (externalSupplyAuditRouteToEventFlow y) :=
    congrArg externalSupplyAuditRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalSupplyAuditRouteRoundTrip x).symm
      (Eq.trans hread (externalSupplyAuditRouteRoundTrip y)))

private theorem externalSupplyAuditRouteFieldsFaithful :
    ∀ x y : ExternalSupplyAuditRouteUp,
      externalSupplyAuditRouteFields x = externalSupplyAuditRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ W₁ G₁ L₁ H₁ P₁ N₁ =>
      cases y with
      | mk B₂ W₂ G₂ L₂ H₂ P₂ N₂ =>
          injection hfields with hB t1
          injection t1 with hW t2
          injection t2 with hG t3
          injection t3 with hL t4
          injection t4 with hH t5
          injection t5 with hP t6
          injection t6 with hN _
          subst hB
          subst hW
          subst hG
          subst hL
          subst hH
          subst hP
          subst hN
          rfl

instance externalSupplyAuditRouteBHistCarrier :
    BHistCarrier ExternalSupplyAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplyAuditRouteToEventFlow
  fromEventFlow := externalSupplyAuditRouteFromEventFlow

instance externalSupplyAuditRouteChapterTasteGate :
    ChapterTasteGate ExternalSupplyAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      externalSupplyAuditRouteFromEventFlow
        (externalSupplyAuditRouteToEventFlow x) = some x
    exact externalSupplyAuditRouteRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplyAuditRouteToEventFlow_injective heq)

instance externalSupplyAuditRouteFieldFaithful :
    FieldFaithful ExternalSupplyAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := externalSupplyAuditRouteFields
  field_faithful := externalSupplyAuditRouteFieldsFaithful

instance externalSupplyAuditRouteNontrivial :
    Nontrivial ExternalSupplyAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplyAuditRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplyAuditRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ExternalSupplyAuditRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  externalSupplyAuditRouteChapterTasteGate

theorem ExternalSupplyAuditRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      externalSupplyAuditRouteDecodeBHist
        (externalSupplyAuditRouteEncodeBHist h) = h) ∧
      (∀ x : ExternalSupplyAuditRouteUp,
        externalSupplyAuditRouteFromEventFlow
          (externalSupplyAuditRouteToEventFlow x) = some x) ∧
      (∀ x y : ExternalSupplyAuditRouteUp,
        externalSupplyAuditRouteToEventFlow x =
          externalSupplyAuditRouteToEventFlow y → x = y) ∧
      Nonempty (FieldFaithful ExternalSupplyAuditRouteUp) ∧
      Nonempty (Nontrivial ExternalSupplyAuditRouteUp) ∧
      externalSupplyAuditRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨externalSupplyAuditRouteDecodeEncodeBHist,
      externalSupplyAuditRouteRoundTrip,
      (fun _ _ heq => externalSupplyAuditRouteToEventFlow_injective heq),
      ⟨externalSupplyAuditRouteFieldFaithful⟩,
      ⟨externalSupplyAuditRouteNontrivial⟩,
      rfl⟩

end BEDC.Derived.ExternalSupplyAuditRouteUp.TasteGate
