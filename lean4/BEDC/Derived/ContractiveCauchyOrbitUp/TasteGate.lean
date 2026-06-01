import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractiveCauchyOrbitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractiveCauchyOrbitUp : Type where
  | mk
      (metric contraction iterate window residual modulus completion endpoint transport
        continuation provenance localName : BHist) : ContractiveCauchyOrbitUp
  deriving DecidableEq

def contractiveCauchyOrbitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractiveCauchyOrbitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractiveCauchyOrbitEncodeBHist h

def contractiveCauchyOrbitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractiveCauchyOrbitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractiveCauchyOrbitDecodeBHist tail)

private theorem ContractiveCauchyOrbitTasteGate_decode_encode :
    ∀ h : BHist,
      contractiveCauchyOrbitDecodeBHist
          (contractiveCauchyOrbitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractiveCauchyOrbitFields : ContractiveCauchyOrbitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractiveCauchyOrbitUp.mk metric contraction iterate window residual modulus
      completion endpoint transport continuation provenance localName =>
      [metric, contraction, iterate, window, residual, modulus, completion, endpoint,
        transport, continuation, provenance, localName]

def contractiveCauchyOrbitToEventFlow : ContractiveCauchyOrbitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contractiveCauchyOrbitFields x).map contractiveCauchyOrbitEncodeBHist

private def contractiveCauchyOrbitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contractiveCauchyOrbitEventAt index rest

def contractiveCauchyOrbitFromEventFlow (ef : EventFlow) :
    Option ContractiveCauchyOrbitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContractiveCauchyOrbitUp.mk
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 0 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 1 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 2 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 3 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 4 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 5 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 6 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 7 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 8 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 9 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 10 ef))
      (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAt 11 ef)))

private theorem ContractiveCauchyOrbitTasteGate_round_trip
    (x : ContractiveCauchyOrbitUp) :
    contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk metric contraction iterate window residual modulus completion endpoint transport
      continuation provenance localName =>
      change
        some
          (ContractiveCauchyOrbitUp.mk
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist metric))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist contraction))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist iterate))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist window))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist residual))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist modulus))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist completion))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist endpoint))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist transport))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist continuation))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist provenance))
            (contractiveCauchyOrbitDecodeBHist
              (contractiveCauchyOrbitEncodeBHist localName))) =
          some
            (ContractiveCauchyOrbitUp.mk metric contraction iterate window residual
              modulus completion endpoint transport continuation provenance localName)
      rw [ContractiveCauchyOrbitTasteGate_decode_encode metric,
        ContractiveCauchyOrbitTasteGate_decode_encode contraction,
        ContractiveCauchyOrbitTasteGate_decode_encode iterate,
        ContractiveCauchyOrbitTasteGate_decode_encode window,
        ContractiveCauchyOrbitTasteGate_decode_encode residual,
        ContractiveCauchyOrbitTasteGate_decode_encode modulus,
        ContractiveCauchyOrbitTasteGate_decode_encode completion,
        ContractiveCauchyOrbitTasteGate_decode_encode endpoint,
        ContractiveCauchyOrbitTasteGate_decode_encode transport,
        ContractiveCauchyOrbitTasteGate_decode_encode continuation,
        ContractiveCauchyOrbitTasteGate_decode_encode provenance,
        ContractiveCauchyOrbitTasteGate_decode_encode localName]

private theorem contractiveCauchyOrbitToEventFlow_injective
    {x y : ContractiveCauchyOrbitUp} :
    contractiveCauchyOrbitToEventFlow x = contractiveCauchyOrbitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
        contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow y) :=
    congrArg contractiveCauchyOrbitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContractiveCauchyOrbitTasteGate_round_trip x).symm
      (Eq.trans hread (ContractiveCauchyOrbitTasteGate_round_trip y)))

private theorem contractiveCauchyOrbit_field_faithful :
    ∀ x y : ContractiveCauchyOrbitUp,
      contractiveCauchyOrbitFields x = contractiveCauchyOrbitFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric contraction iterate window residual modulus completion endpoint transport
      continuation provenance localName =>
      cases y with
      | mk metric' contraction' iterate' window' residual' modulus' completion'
          endpoint' transport' continuation' provenance' localName' =>
          cases hfields
          rfl

instance contractiveCauchyOrbitBHistCarrier :
    BHistCarrier ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractiveCauchyOrbitToEventFlow
  fromEventFlow := contractiveCauchyOrbitFromEventFlow

instance contractiveCauchyOrbitChapterTasteGate :
    ChapterTasteGate ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
        some x
    exact ContractiveCauchyOrbitTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contractiveCauchyOrbitToEventFlow_injective heq)

instance contractiveCauchyOrbitFieldFaithful :
    FieldFaithful ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contractiveCauchyOrbitFields
  field_faithful := contractiveCauchyOrbit_field_faithful

instance contractiveCauchyOrbitNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContractiveCauchyOrbitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ContractiveCauchyOrbitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContractiveCauchyOrbitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contractiveCauchyOrbitChapterTasteGate

theorem ContractiveCauchyOrbitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ContractiveCauchyOrbitUp) ∧
      Nonempty (FieldFaithful ContractiveCauchyOrbitUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ContractiveCauchyOrbitUp) ∧
      (∀ h : BHist,
        contractiveCauchyOrbitDecodeBHist
            (contractiveCauchyOrbitEncodeBHist h) =
          h) ∧
      (∀ x : ContractiveCauchyOrbitUp,
        contractiveCauchyOrbitFromEventFlow
            (contractiveCauchyOrbitToEventFlow x) =
          some x) ∧
      (∀ x y : ContractiveCauchyOrbitUp,
        contractiveCauchyOrbitToEventFlow x =
            contractiveCauchyOrbitToEventFlow y →
          x = y) ∧
      contractiveCauchyOrbitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨contractiveCauchyOrbitChapterTasteGate⟩,
      ⟨contractiveCauchyOrbitFieldFaithful⟩,
      ⟨contractiveCauchyOrbitNontrivial⟩,
      ContractiveCauchyOrbitTasteGate_decode_encode,
      ContractiveCauchyOrbitTasteGate_round_trip,
      (fun _ _ heq => contractiveCauchyOrbitToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContractiveCauchyOrbitUp
