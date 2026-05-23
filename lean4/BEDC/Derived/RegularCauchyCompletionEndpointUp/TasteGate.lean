import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionEndpointUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionEndpointUp : Type where
  | mk (B L X U R H C P N : BHist) : RegularCauchyCompletionEndpointUp
  deriving DecidableEq

def regularCauchyCompletionEndpointEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionEndpointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionEndpointEncodeBHist h

def regularCauchyCompletionEndpointDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionEndpointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionEndpointDecodeBHist tail)

private theorem regularCauchyCompletionEndpoint_decode_encode_bhist :
    forall h : BHist,
      regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionEndpointFields :
    RegularCauchyCompletionEndpointUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionEndpointUp.mk B L X U R H C P N => [B, L, X, U, R, H, C, P, N]

def regularCauchyCompletionEndpointToEventFlow :
    RegularCauchyCompletionEndpointUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyCompletionEndpointFields x).map
      regularCauchyCompletionEndpointEncodeBHist

private def regularCauchyCompletionEndpointEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCompletionEndpointEventAt index rest

def regularCauchyCompletionEndpointFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCompletionEndpointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCompletionEndpointUp.mk
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 0 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 1 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 2 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 3 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 4 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 5 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 6 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 7 ef))
      (regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEventAt 8 ef)))

private theorem regularCauchyCompletionEndpoint_round_trip
    (x : RegularCauchyCompletionEndpointUp) :
    regularCauchyCompletionEndpointFromEventFlow
        (regularCauchyCompletionEndpointToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B L X U R H C P N =>
      change
        some
          (RegularCauchyCompletionEndpointUp.mk
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist B))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist L))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist X))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist U))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist R))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist H))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist C))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist P))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist N))) =
          some (RegularCauchyCompletionEndpointUp.mk B L X U R H C P N)
      rw [regularCauchyCompletionEndpoint_decode_encode_bhist B,
        regularCauchyCompletionEndpoint_decode_encode_bhist L,
        regularCauchyCompletionEndpoint_decode_encode_bhist X,
        regularCauchyCompletionEndpoint_decode_encode_bhist U,
        regularCauchyCompletionEndpoint_decode_encode_bhist R,
        regularCauchyCompletionEndpoint_decode_encode_bhist H,
        regularCauchyCompletionEndpoint_decode_encode_bhist C,
        regularCauchyCompletionEndpoint_decode_encode_bhist P,
        regularCauchyCompletionEndpoint_decode_encode_bhist N]

private theorem regularCauchyCompletionEndpointToEventFlow_injective
    {x y : RegularCauchyCompletionEndpointUp} :
    regularCauchyCompletionEndpointToEventFlow x =
        regularCauchyCompletionEndpointToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionEndpointFromEventFlow
          (regularCauchyCompletionEndpointToEventFlow x) =
        regularCauchyCompletionEndpointFromEventFlow
          (regularCauchyCompletionEndpointToEventFlow y) :=
    congrArg regularCauchyCompletionEndpointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionEndpoint_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionEndpoint_round_trip y)))

private theorem regularCauchyCompletionEndpoint_fields_faithful :
    forall x y : RegularCauchyCompletionEndpointUp,
      regularCauchyCompletionEndpointFields x = regularCauchyCompletionEndpointFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 L1 X1 U1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 L2 X2 U2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyCompletionEndpointBHistCarrier :
    BHistCarrier RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionEndpointToEventFlow
  fromEventFlow := regularCauchyCompletionEndpointFromEventFlow

instance regularCauchyCompletionEndpointChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionEndpointFromEventFlow
          (regularCauchyCompletionEndpointToEventFlow x) =
        some x
    exact regularCauchyCompletionEndpoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionEndpointToEventFlow_injective heq)

instance regularCauchyCompletionEndpointFieldFaithful :
    FieldFaithful RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCompletionEndpointFields
  field_faithful := regularCauchyCompletionEndpoint_fields_faithful

instance regularCauchyCompletionEndpointNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionEndpointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCompletionEndpointUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment :
    (forall h : BHist,
        regularCauchyCompletionEndpointDecodeBHist
            (regularCauchyCompletionEndpointEncodeBHist h) =
          h) ∧
      (forall x : RegularCauchyCompletionEndpointUp,
        regularCauchyCompletionEndpointFromEventFlow
            (regularCauchyCompletionEndpointToEventFlow x) =
          some x) ∧
      (forall x y : RegularCauchyCompletionEndpointUp,
        regularCauchyCompletionEndpointToEventFlow x =
            regularCauchyCompletionEndpointToEventFlow y ->
          x = y) ∧
      regularCauchyCompletionEndpointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨regularCauchyCompletionEndpoint_decode_encode_bhist,
      regularCauchyCompletionEndpoint_round_trip,
      (fun _ _ heq => regularCauchyCompletionEndpointToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionEndpointUp.TasteGate
