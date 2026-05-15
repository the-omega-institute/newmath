import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverBridgeLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverBridgeLedgerUp : Type where
  | mk :
      (state boundary multi identity locality route transport cont pkg name : BHist) →
      ObserverBridgeLedgerUp

private def observerBridgeLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerBridgeLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerBridgeLedgerEncodeBHist h

private def observerBridgeLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerBridgeLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerBridgeLedgerDecodeBHist tail)

private theorem observerBridgeLedger_decode_encode_bhist :
    ∀ h : BHist, observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def observerBridgeLedgerToEventFlow : ObserverBridgeLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverBridgeLedgerUp.mk state boundary multi identity locality route transport cont pkg name =>
      [[BMark.b0],
        observerBridgeLedgerEncodeBHist state,
        [BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist multi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist identity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerBridgeLedgerEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist pkg,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observerBridgeLedgerEncodeBHist name]

private def observerBridgeLedgerFromEventFlow : EventFlow → Option ObserverBridgeLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, state, _tag1, boundary, _tag2, multi, _tag3, identity, _tag4, locality,
      _tag5, route, _tag6, transport, _tag7, cont, _tag8, pkg, _tag9, name] =>
      some
        (ObserverBridgeLedgerUp.mk
          (observerBridgeLedgerDecodeBHist state)
          (observerBridgeLedgerDecodeBHist boundary)
          (observerBridgeLedgerDecodeBHist multi)
          (observerBridgeLedgerDecodeBHist identity)
          (observerBridgeLedgerDecodeBHist locality)
          (observerBridgeLedgerDecodeBHist route)
          (observerBridgeLedgerDecodeBHist transport)
          (observerBridgeLedgerDecodeBHist cont)
          (observerBridgeLedgerDecodeBHist pkg)
          (observerBridgeLedgerDecodeBHist name))
  | _ => none

private theorem observerBridgeLedger_round_trip :
    ∀ x : ObserverBridgeLedgerUp,
      observerBridgeLedgerFromEventFlow (observerBridgeLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk state boundary multi identity locality route transport cont pkg name =>
      change
        some
          (ObserverBridgeLedgerUp.mk
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist state))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist boundary))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist multi))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist identity))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist locality))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist route))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist transport))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist cont))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist pkg))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist name))) =
          some
            (ObserverBridgeLedgerUp.mk state boundary multi identity locality route transport
              cont pkg name)
      rw [observerBridgeLedger_decode_encode_bhist state,
        observerBridgeLedger_decode_encode_bhist boundary,
        observerBridgeLedger_decode_encode_bhist multi,
        observerBridgeLedger_decode_encode_bhist identity,
        observerBridgeLedger_decode_encode_bhist locality,
        observerBridgeLedger_decode_encode_bhist route,
        observerBridgeLedger_decode_encode_bhist transport,
        observerBridgeLedger_decode_encode_bhist cont,
        observerBridgeLedger_decode_encode_bhist pkg,
        observerBridgeLedger_decode_encode_bhist name]

private theorem observerBridgeLedgerToEventFlow_injective {x y : ObserverBridgeLedgerUp} :
    observerBridgeLedgerToEventFlow x = observerBridgeLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerBridgeLedgerFromEventFlow (observerBridgeLedgerToEventFlow x) =
        observerBridgeLedgerFromEventFlow (observerBridgeLedgerToEventFlow y) :=
    congrArg observerBridgeLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerBridgeLedger_round_trip x).symm
      (Eq.trans hread (observerBridgeLedger_round_trip y)))

private def observerBridgeLedgerFields : ObserverBridgeLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverBridgeLedgerUp.mk state boundary multi identity locality route transport cont pkg name =>
      [state, boundary, multi, identity, locality, route, transport, cont, pkg, name]

private theorem observerBridgeLedger_field_faithful :
    ∀ x y : ObserverBridgeLedgerUp,
      observerBridgeLedgerFields x = observerBridgeLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk state₁ boundary₁ multi₁ identity₁ locality₁ route₁ transport₁ cont₁ pkg₁ name₁ =>
      cases y with
      | mk state₂ boundary₂ multi₂ identity₂ locality₂ route₂ transport₂ cont₂ pkg₂ name₂ =>
          cases h
          rfl

instance observerBridgeLedgerBHistCarrier : BHistCarrier ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerBridgeLedgerToEventFlow
  fromEventFlow := observerBridgeLedgerFromEventFlow

instance observerBridgeLedgerChapterTasteGate : ChapterTasteGate ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerBridgeLedgerFromEventFlow (observerBridgeLedgerToEventFlow x) = some x
    exact observerBridgeLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerBridgeLedgerToEventFlow_injective heq)

instance observerBridgeLedgerFieldFaithful : FieldFaithful ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerBridgeLedgerFields
  field_faithful := observerBridgeLedger_field_faithful

instance observerBridgeLedgerNontrivial : Nontrivial ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverBridgeLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverBridgeLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverBridgeLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerBridgeLedgerChapterTasteGate

end BEDC.Derived.ObserverBridgeLedgerUp
