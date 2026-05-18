import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplySocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplySocketUp : Type where
  | mk :
      (boundary apophatic classifier router refusal ledger transport route provenance
        localName : BHist) →
      ExternalSupplySocketUp
  deriving DecidableEq

def externalSupplySocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplySocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplySocketEncodeBHist h

def externalSupplySocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplySocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplySocketDecodeBHist tail)

private def externalSupplySocketRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => externalSupplySocketRawAt n rest

private theorem externalSupplySocket_decode_encode_bhist :
    ∀ h : BHist,
      externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def externalSupplySocketFields : ExternalSupplySocketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplySocketUp.mk boundary apophatic classifier router refusal ledger transport
      route provenance localName =>
      [boundary, apophatic, classifier, router, refusal, ledger, transport, route,
        provenance, localName]

def externalSupplySocketToEventFlow : ExternalSupplySocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplySocketUp.mk boundary apophatic classifier router refusal ledger transport
      route provenance localName =>
      [[BMark.b0],
        externalSupplySocketEncodeBHist boundary,
        [BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist apophatic,
        [BMark.b1, BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist router,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        externalSupplySocketEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        externalSupplySocketEncodeBHist localName]

def externalSupplySocketFromEventFlow :
    EventFlow → Option ExternalSupplySocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ExternalSupplySocketUp.mk
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 1 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 3 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 5 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 7 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 9 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 11 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 13 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 15 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 17 ef))
          (externalSupplySocketDecodeBHist (externalSupplySocketRawAt 19 ef)))

private theorem externalSupplySocket_round_trip :
    ∀ x : ExternalSupplySocketUp,
      externalSupplySocketFromEventFlow (externalSupplySocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundary apophatic classifier router refusal ledger transport route provenance localName =>
      change
        some
          (ExternalSupplySocketUp.mk
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist boundary))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist apophatic))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist classifier))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist router))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist refusal))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist ledger))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist transport))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist route))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist provenance))
            (externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist localName))) =
          some
            (ExternalSupplySocketUp.mk boundary apophatic classifier router refusal ledger
              transport route provenance localName)
      rw [externalSupplySocket_decode_encode_bhist boundary,
        externalSupplySocket_decode_encode_bhist apophatic,
        externalSupplySocket_decode_encode_bhist classifier,
        externalSupplySocket_decode_encode_bhist router,
        externalSupplySocket_decode_encode_bhist refusal,
        externalSupplySocket_decode_encode_bhist ledger,
        externalSupplySocket_decode_encode_bhist transport,
        externalSupplySocket_decode_encode_bhist route,
        externalSupplySocket_decode_encode_bhist provenance,
        externalSupplySocket_decode_encode_bhist localName]

private theorem externalSupplySocketToEventFlow_injective
    {x y : ExternalSupplySocketUp} :
    externalSupplySocketToEventFlow x = externalSupplySocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplySocketFromEventFlow (externalSupplySocketToEventFlow x) =
        externalSupplySocketFromEventFlow (externalSupplySocketToEventFlow y) :=
    congrArg externalSupplySocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalSupplySocket_round_trip x).symm
      (Eq.trans hread (externalSupplySocket_round_trip y)))

private theorem ExternalSupplySocketTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ExternalSupplySocketUp,
      externalSupplySocketFields x = externalSupplySocketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk boundary apophatic classifier router refusal ledger transport route provenance localName =>
      cases y with
      | mk boundary' apophatic' classifier' router' refusal' ledger' transport' route'
          provenance' localName' =>
          cases hfields
          rfl

instance externalSupplySocketBHistCarrier :
    BHistCarrier ExternalSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplySocketToEventFlow
  fromEventFlow := externalSupplySocketFromEventFlow

instance externalSupplySocketChapterTasteGate :
    ChapterTasteGate ExternalSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change externalSupplySocketFromEventFlow (externalSupplySocketToEventFlow x) = some x
    exact externalSupplySocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplySocketToEventFlow_injective heq)

instance externalSupplySocketFieldFaithful :
    FieldFaithful ExternalSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := externalSupplySocketFields
  field_faithful := ExternalSupplySocketTasteGate_single_carrier_alignment_field_faithful

instance externalSupplySocketNontrivial :
    Nontrivial ExternalSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplySocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplySocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ExternalSupplySocketTasteGate_single_carrier_alignment :
    (∀ h : BHist, externalSupplySocketDecodeBHist (externalSupplySocketEncodeBHist h) = h) ∧
      (∀ x : ExternalSupplySocketUp,
        externalSupplySocketFromEventFlow (externalSupplySocketToEventFlow x) = some x) ∧
        (∀ x y : ExternalSupplySocketUp,
          externalSupplySocketToEventFlow x = externalSupplySocketToEventFlow y → x = y) ∧
          externalSupplySocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact externalSupplySocket_decode_encode_bhist
  · constructor
    · exact externalSupplySocket_round_trip
    · constructor
      · intro x y heq
        exact externalSupplySocketToEventFlow_injective heq
      · rfl

end BEDC.Derived.ExternalSupplySocketUp
