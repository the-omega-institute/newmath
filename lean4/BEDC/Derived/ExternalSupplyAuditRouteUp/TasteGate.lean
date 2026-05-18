import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplyAuditRouteUp

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

private theorem externalSupplyAuditRoute_decode_encode_bhist :
    ∀ h : BHist,
      externalSupplyAuditRouteDecodeBHist
        (externalSupplyAuditRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem externalSupplyAuditRoute_mk_congr
    {B B' W W' G G' L L' H H' P P' N N' : BHist}
    (hB : B' = B) (hW : W' = W) (hG : G' = G) (hL : L' = L)
    (hH : H' = H) (hP : P' = P) (hN : N' = N) :
    ExternalSupplyAuditRouteUp.mk B' W' G' L' H' P' N' =
      ExternalSupplyAuditRouteUp.mk B W G L H P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hW
  cases hG
  cases hL
  cases hH
  cases hP
  cases hN
  rfl

private def externalSupplyAuditRouteFields :
    ExternalSupplyAuditRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplyAuditRouteUp.mk B W G L H P N => [B, W, G, L, H, P, N]

def externalSupplyAuditRouteToEventFlow :
    ExternalSupplyAuditRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (externalSupplyAuditRouteFields x).map externalSupplyAuditRouteEncodeBHist

private def externalSupplyAuditRouteEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => externalSupplyAuditRouteEventAtDefault index rest

def externalSupplyAuditRouteFromEventFlow :
    EventFlow → Option ExternalSupplyAuditRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ExternalSupplyAuditRouteUp.mk
        (externalSupplyAuditRouteDecodeBHist
          (externalSupplyAuditRouteEventAtDefault 0 ef))
        (externalSupplyAuditRouteDecodeBHist
          (externalSupplyAuditRouteEventAtDefault 1 ef))
        (externalSupplyAuditRouteDecodeBHist
          (externalSupplyAuditRouteEventAtDefault 2 ef))
        (externalSupplyAuditRouteDecodeBHist
          (externalSupplyAuditRouteEventAtDefault 3 ef))
        (externalSupplyAuditRouteDecodeBHist
          (externalSupplyAuditRouteEventAtDefault 4 ef))
        (externalSupplyAuditRouteDecodeBHist
          (externalSupplyAuditRouteEventAtDefault 5 ef))
        (externalSupplyAuditRouteDecodeBHist
          (externalSupplyAuditRouteEventAtDefault 6 ef)))

private theorem externalSupplyAuditRoute_round_trip :
    ∀ x : ExternalSupplyAuditRouteUp,
      externalSupplyAuditRouteFromEventFlow
        (externalSupplyAuditRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B W G L H P N =>
      exact
        congrArg some
          (externalSupplyAuditRoute_mk_congr
            (externalSupplyAuditRoute_decode_encode_bhist B)
            (externalSupplyAuditRoute_decode_encode_bhist W)
            (externalSupplyAuditRoute_decode_encode_bhist G)
            (externalSupplyAuditRoute_decode_encode_bhist L)
            (externalSupplyAuditRoute_decode_encode_bhist H)
            (externalSupplyAuditRoute_decode_encode_bhist P)
            (externalSupplyAuditRoute_decode_encode_bhist N))

private theorem externalSupplyAuditRouteToEventFlow_injective
    {x y : ExternalSupplyAuditRouteUp} :
    externalSupplyAuditRouteToEventFlow x =
      externalSupplyAuditRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplyAuditRouteFromEventFlow (externalSupplyAuditRouteToEventFlow x) =
        externalSupplyAuditRouteFromEventFlow (externalSupplyAuditRouteToEventFlow y) :=
    congrArg externalSupplyAuditRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalSupplyAuditRoute_round_trip x).symm
      (Eq.trans hread (externalSupplyAuditRoute_round_trip y)))

private theorem externalSupplyAuditRoute_field_faithful :
    ∀ x y : ExternalSupplyAuditRouteUp,
      externalSupplyAuditRouteFields x = externalSupplyAuditRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B W G L H P N =>
      cases y with
      | mk B' W' G' L' H' P' N' =>
          cases hfields
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
    exact externalSupplyAuditRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplyAuditRouteToEventFlow_injective heq)

instance externalSupplyAuditRouteFieldFaithful :
    FieldFaithful ExternalSupplyAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := externalSupplyAuditRouteFields
  field_faithful := externalSupplyAuditRoute_field_faithful

instance externalSupplyAuditRouteNontrivial :
    Nontrivial ExternalSupplyAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplyAuditRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplyAuditRouteUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
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
              externalSupplyAuditRouteToEventFlow y →
            x = y) ∧
          externalSupplyAuditRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨externalSupplyAuditRoute_decode_encode_bhist,
      externalSupplyAuditRoute_round_trip,
      (fun _ _ heq => externalSupplyAuditRouteToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ExternalSupplyAuditRouteUp
