import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReductionFuelBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReductionFuelBoundaryUp : Type where
  | mk : (host fuel trace endpoint timeout audit transport routes provenance name : BHist) →
      ReductionFuelBoundaryUp
  deriving DecidableEq

def reductionFuelBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reductionFuelBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reductionFuelBoundaryEncodeBHist h

def reductionFuelBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reductionFuelBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reductionFuelBoundaryDecodeBHist tail)

private theorem reductionFuelBoundary_decode_encode_bhist :
    ∀ h : BHist,
      reductionFuelBoundaryDecodeBHist (reductionFuelBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def reductionFuelBoundaryFields : ReductionFuelBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReductionFuelBoundaryUp.mk host fuel trace endpoint timeout audit transport routes
      provenance name =>
      [host, fuel, trace, endpoint, timeout, audit, transport, routes, provenance, name]

def reductionFuelBoundaryToEventFlow : ReductionFuelBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (reductionFuelBoundaryFields x).map reductionFuelBoundaryEncodeBHist

private def reductionFuelBoundaryDecodePacket
    (host fuel trace endpoint timeout audit transport routes provenance name : RawEvent) :
    ReductionFuelBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ReductionFuelBoundaryUp.mk
    (reductionFuelBoundaryDecodeBHist host)
    (reductionFuelBoundaryDecodeBHist fuel)
    (reductionFuelBoundaryDecodeBHist trace)
    (reductionFuelBoundaryDecodeBHist endpoint)
    (reductionFuelBoundaryDecodeBHist timeout)
    (reductionFuelBoundaryDecodeBHist audit)
    (reductionFuelBoundaryDecodeBHist transport)
    (reductionFuelBoundaryDecodeBHist routes)
    (reductionFuelBoundaryDecodeBHist provenance)
    (reductionFuelBoundaryDecodeBHist name)

private def reductionFuelBoundaryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => reductionFuelBoundaryRawAt n rest

private def reductionFuelBoundaryLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => reductionFuelBoundaryLengthEq n rest

def reductionFuelBoundaryFromEventFlow : EventFlow → Option ReductionFuelBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match reductionFuelBoundaryLengthEq 10 flow with
      | true =>
          some
            (reductionFuelBoundaryDecodePacket
              (reductionFuelBoundaryRawAt 0 flow)
              (reductionFuelBoundaryRawAt 1 flow)
              (reductionFuelBoundaryRawAt 2 flow)
              (reductionFuelBoundaryRawAt 3 flow)
              (reductionFuelBoundaryRawAt 4 flow)
              (reductionFuelBoundaryRawAt 5 flow)
              (reductionFuelBoundaryRawAt 6 flow)
              (reductionFuelBoundaryRawAt 7 flow)
              (reductionFuelBoundaryRawAt 8 flow)
              (reductionFuelBoundaryRawAt 9 flow))
      | false => none

private theorem reductionFuelBoundary_round_trip :
    ∀ x : ReductionFuelBoundaryUp,
      reductionFuelBoundaryFromEventFlow
        (reductionFuelBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk host fuel trace endpoint timeout audit transport routes provenance name =>
      change
        some
          (reductionFuelBoundaryDecodePacket
            (reductionFuelBoundaryEncodeBHist host)
            (reductionFuelBoundaryEncodeBHist fuel)
            (reductionFuelBoundaryEncodeBHist trace)
            (reductionFuelBoundaryEncodeBHist endpoint)
            (reductionFuelBoundaryEncodeBHist timeout)
            (reductionFuelBoundaryEncodeBHist audit)
            (reductionFuelBoundaryEncodeBHist transport)
            (reductionFuelBoundaryEncodeBHist routes)
            (reductionFuelBoundaryEncodeBHist provenance)
            (reductionFuelBoundaryEncodeBHist name)) =
          some
            (ReductionFuelBoundaryUp.mk host fuel trace endpoint timeout audit transport
              routes provenance name)
      unfold reductionFuelBoundaryDecodePacket
      rw [reductionFuelBoundary_decode_encode_bhist host,
        reductionFuelBoundary_decode_encode_bhist fuel,
        reductionFuelBoundary_decode_encode_bhist trace,
        reductionFuelBoundary_decode_encode_bhist endpoint,
        reductionFuelBoundary_decode_encode_bhist timeout,
        reductionFuelBoundary_decode_encode_bhist audit,
        reductionFuelBoundary_decode_encode_bhist transport,
        reductionFuelBoundary_decode_encode_bhist routes,
        reductionFuelBoundary_decode_encode_bhist provenance,
        reductionFuelBoundary_decode_encode_bhist name]

private theorem reductionFuelBoundaryToEventFlow_injective
    {x y : ReductionFuelBoundaryUp} :
    reductionFuelBoundaryToEventFlow x =
      reductionFuelBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reductionFuelBoundaryFromEventFlow
          (reductionFuelBoundaryToEventFlow x) =
        reductionFuelBoundaryFromEventFlow
          (reductionFuelBoundaryToEventFlow y) :=
    congrArg reductionFuelBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reductionFuelBoundary_round_trip x).symm
      (Eq.trans hread (reductionFuelBoundary_round_trip y)))

private theorem reductionFuelBoundary_fields_faithful :
    ∀ x y : ReductionFuelBoundaryUp,
      reductionFuelBoundaryFields x = reductionFuelBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk host₁ fuel₁ trace₁ endpoint₁ timeout₁ audit₁ transport₁ routes₁ provenance₁ name₁ =>
      cases y with
      | mk host₂ fuel₂ trace₂ endpoint₂ timeout₂ audit₂ transport₂ routes₂ provenance₂
          name₂ =>
          cases hfields
          rfl

instance reductionFuelBoundaryBHistCarrier :
    BHistCarrier ReductionFuelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reductionFuelBoundaryToEventFlow
  fromEventFlow := reductionFuelBoundaryFromEventFlow

instance reductionFuelBoundaryChapterTasteGate :
    ChapterTasteGate ReductionFuelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      reductionFuelBoundaryFromEventFlow
        (reductionFuelBoundaryToEventFlow x) = some x
    exact reductionFuelBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reductionFuelBoundaryToEventFlow_injective heq)

instance reductionFuelBoundaryFieldFaithful :
    FieldFaithful ReductionFuelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reductionFuelBoundaryFields
  field_faithful := reductionFuelBoundary_fields_faithful

instance reductionFuelBoundaryNontrivial :
    Nontrivial ReductionFuelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReductionFuelBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ReductionFuelBoundaryUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ReductionFuelBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  reductionFuelBoundaryChapterTasteGate

theorem ReductionFuelBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ReductionFuelBoundaryUp) ∧
      Nonempty (FieldFaithful ReductionFuelBoundaryUp) ∧
        Nonempty (Nontrivial ReductionFuelBoundaryUp) ∧
          (∀ h : BHist,
            reductionFuelBoundaryDecodeBHist
              (reductionFuelBoundaryEncodeBHist h) = h) ∧
            (∀ x : ReductionFuelBoundaryUp,
              reductionFuelBoundaryFromEventFlow
                (reductionFuelBoundaryToEventFlow x) = some x) ∧
              (∀ x y : ReductionFuelBoundaryUp,
                reductionFuelBoundaryToEventFlow x =
                    reductionFuelBoundaryToEventFlow y →
                  x = y) ∧
                reductionFuelBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨reductionFuelBoundaryChapterTasteGate⟩,
      ⟨reductionFuelBoundaryFieldFaithful⟩,
      ⟨reductionFuelBoundaryNontrivial⟩,
      reductionFuelBoundary_decode_encode_bhist,
      reductionFuelBoundary_round_trip,
      (fun _ _ heq => reductionFuelBoundaryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ReductionFuelBoundaryUp
