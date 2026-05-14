import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverDirectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverDirectionUp : Type where
  | mk :
      (observer target direction licensedComparison readback transport route provenance
        localName : BHist) →
      ObserverDirectionUp
  deriving DecidableEq

def observerDirectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerDirectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerDirectionEncodeBHist h

def observerDirectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerDirectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerDirectionDecodeBHist tail)

private theorem observerDirectionDecode_encode_bhist :
    ∀ h : BHist, observerDirectionDecodeBHist (observerDirectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observerDirectionFields : ObserverDirectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverDirectionUp.mk observer target direction licensedComparison readback transport
      route provenance localName =>
      [observer, target, direction, licensedComparison, readback, transport, route,
        provenance, localName]

def observerDirectionToEventFlow : ObserverDirectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverDirectionUp.mk observer target direction licensedComparison readback transport
      route provenance localName =>
      [[BMark.b0],
        observerDirectionEncodeBHist observer,
        [BMark.b1, BMark.b0],
        observerDirectionEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist direction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist licensedComparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerDirectionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerDirectionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observerDirectionEncodeBHist localName]

def observerDirectionFromEventFlow : EventFlow → Option ObserverDirectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observer :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | direction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | licensedComparison :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ObserverDirectionUp.mk
                                                                                  (observerDirectionDecodeBHist
                                                                                    observer)
                                                                                  (observerDirectionDecodeBHist
                                                                                    target)
                                                                                  (observerDirectionDecodeBHist
                                                                                    direction)
                                                                                  (observerDirectionDecodeBHist
                                                                                    licensedComparison)
                                                                                  (observerDirectionDecodeBHist
                                                                                    readback)
                                                                                  (observerDirectionDecodeBHist
                                                                                    transport)
                                                                                  (observerDirectionDecodeBHist
                                                                                    route)
                                                                                  (observerDirectionDecodeBHist
                                                                                    provenance)
                                                                                  (observerDirectionDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem observerDirection_round_trip :
    ∀ x : ObserverDirectionUp,
      observerDirectionFromEventFlow (observerDirectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observer target direction licensedComparison readback transport route provenance
      localName =>
      change
        some
          (ObserverDirectionUp.mk
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist observer))
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist target))
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist direction))
            (observerDirectionDecodeBHist
              (observerDirectionEncodeBHist licensedComparison))
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist readback))
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist transport))
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist route))
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist provenance))
            (observerDirectionDecodeBHist (observerDirectionEncodeBHist localName))) =
          some
            (ObserverDirectionUp.mk observer target direction licensedComparison readback
              transport route provenance localName)
      rw [observerDirectionDecode_encode_bhist observer,
        observerDirectionDecode_encode_bhist target,
        observerDirectionDecode_encode_bhist direction,
        observerDirectionDecode_encode_bhist licensedComparison,
        observerDirectionDecode_encode_bhist readback,
        observerDirectionDecode_encode_bhist transport,
        observerDirectionDecode_encode_bhist route,
        observerDirectionDecode_encode_bhist provenance,
        observerDirectionDecode_encode_bhist localName]

private theorem observerDirectionToEventFlow_injective {x y : ObserverDirectionUp} :
    observerDirectionToEventFlow x = observerDirectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerDirectionFromEventFlow (observerDirectionToEventFlow x) =
        observerDirectionFromEventFlow (observerDirectionToEventFlow y) :=
    congrArg observerDirectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerDirection_round_trip x).symm
      (Eq.trans hread (observerDirection_round_trip y)))

private theorem ObserverDirectionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ObserverDirectionUp, observerDirectionFields x = observerDirectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observer target direction licensedComparison readback transport route provenance
      localName =>
      cases y with
      | mk observer' target' direction' licensedComparison' readback' transport' route'
          provenance' localName' =>
          cases hfields
          rfl

instance observerDirectionBHistCarrier : BHistCarrier ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerDirectionToEventFlow
  fromEventFlow := observerDirectionFromEventFlow

instance observerDirectionChapterTasteGate : ChapterTasteGate ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerDirectionFromEventFlow (observerDirectionToEventFlow x) = some x
    exact observerDirection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerDirectionToEventFlow_injective heq)

instance observerDirectionFieldFaithful : FieldFaithful ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerDirectionFields
  field_faithful := ObserverDirectionTasteGate_single_carrier_alignment_field_faithful

instance observerDirectionNontrivial : Nontrivial ObserverDirectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverDirectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverDirectionUp.mk BHist.Empty BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverDirectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerDirectionChapterTasteGate

namespace TasteGate

theorem ObserverDirectionTasteGate_single_carrier_alignment :
    (forall h : BHist, observerDirectionDecodeBHist (observerDirectionEncodeBHist h) = h) /\
      (forall x : ObserverDirectionUp,
        observerDirectionFromEventFlow (observerDirectionToEventFlow x) = some x) /\
      (forall x y : ObserverDirectionUp,
        observerDirectionToEventFlow x = observerDirectionToEventFlow y -> x = y) /\
      Nonempty (ChapterTasteGate ObserverDirectionUp) /\
      Nonempty (FieldFaithful ObserverDirectionUp) /\
      Nonempty (Nontrivial ObserverDirectionUp) /\
      observerDirectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerDirectionDecode_encode_bhist
  · constructor
    · exact observerDirection_round_trip
    · constructor
      · intro x y heq
        exact observerDirectionToEventFlow_injective heq
      · constructor
        · exact ⟨observerDirectionChapterTasteGate⟩
        · constructor
          · exact ⟨observerDirectionFieldFaithful⟩
          · constructor
            · exact ⟨observerDirectionNontrivial⟩
            · rfl

end TasteGate

end BEDC.Derived.ObserverDirectionUp
