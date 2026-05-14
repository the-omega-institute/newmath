import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SocketKindClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SocketKindClassifierUp : Type where
  | mk :
      (socketSite kind requestedSupply gateLocality transport route provenance nameCert :
        BHist) →
      SocketKindClassifierUp
  deriving DecidableEq

private def socketKindClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: socketKindClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: socketKindClassifierEncodeBHist h

private def socketKindClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (socketKindClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (socketKindClassifierDecodeBHist tail)

private theorem socketKindClassifier_decode_encode_bhist :
    ∀ h : BHist,
      socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def socketKindClassifierToEventFlow : SocketKindClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SocketKindClassifierUp.mk socketSite kind requestedSupply gateLocality transport route
      provenance nameCert =>
      [[BMark.b0],
        socketKindClassifierEncodeBHist socketSite,
        [BMark.b1, BMark.b0],
        socketKindClassifierEncodeBHist kind,
        [BMark.b1, BMark.b1, BMark.b0],
        socketKindClassifierEncodeBHist requestedSupply,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        socketKindClassifierEncodeBHist gateLocality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        socketKindClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        socketKindClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        socketKindClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        socketKindClassifierEncodeBHist nameCert]

private def socketKindClassifierFromEventFlow :
    EventFlow → Option SocketKindClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | socketSite :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | kind :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | requestedSupply :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gateLocality :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (SocketKindClassifierUp.mk
                                                                          (socketKindClassifierDecodeBHist
                                                                            socketSite)
                                                                          (socketKindClassifierDecodeBHist
                                                                            kind)
                                                                          (socketKindClassifierDecodeBHist
                                                                            requestedSupply)
                                                                          (socketKindClassifierDecodeBHist
                                                                            gateLocality)
                                                                          (socketKindClassifierDecodeBHist
                                                                            transport)
                                                                          (socketKindClassifierDecodeBHist
                                                                            route)
                                                                          (socketKindClassifierDecodeBHist
                                                                            provenance)
                                                                          (socketKindClassifierDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem socketKindClassifier_round_trip :
    ∀ x : SocketKindClassifierUp,
      socketKindClassifierFromEventFlow (socketKindClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk socketSite kind requestedSupply gateLocality transport route provenance nameCert =>
      change
        some
          (SocketKindClassifierUp.mk
            (socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist socketSite))
            (socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist kind))
            (socketKindClassifierDecodeBHist
              (socketKindClassifierEncodeBHist requestedSupply))
            (socketKindClassifierDecodeBHist
              (socketKindClassifierEncodeBHist gateLocality))
            (socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist transport))
            (socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist route))
            (socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist provenance))
            (socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist nameCert))) =
          some
            (SocketKindClassifierUp.mk socketSite kind requestedSupply gateLocality transport
              route provenance nameCert)
      rw [socketKindClassifier_decode_encode_bhist socketSite,
        socketKindClassifier_decode_encode_bhist kind,
        socketKindClassifier_decode_encode_bhist requestedSupply,
        socketKindClassifier_decode_encode_bhist gateLocality,
        socketKindClassifier_decode_encode_bhist transport,
        socketKindClassifier_decode_encode_bhist route,
        socketKindClassifier_decode_encode_bhist provenance,
        socketKindClassifier_decode_encode_bhist nameCert]

private theorem socketKindClassifierToEventFlow_injective
    {x y : SocketKindClassifierUp} :
    socketKindClassifierToEventFlow x = socketKindClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      socketKindClassifierFromEventFlow (socketKindClassifierToEventFlow x) =
        socketKindClassifierFromEventFlow (socketKindClassifierToEventFlow y) :=
    congrArg socketKindClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (socketKindClassifier_round_trip x).symm
      (Eq.trans hread (socketKindClassifier_round_trip y)))

private def socketKindClassifierFields :
    SocketKindClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SocketKindClassifierUp.mk socketSite kind requestedSupply gateLocality transport route
      provenance nameCert =>
      [socketSite, kind, requestedSupply, gateLocality, transport, route, provenance,
        nameCert]

private theorem socketKindClassifier_field_faithful :
    ∀ x y : SocketKindClassifierUp,
      socketKindClassifierFields x = socketKindClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk socketSite kind requestedSupply gateLocality transport route provenance nameCert =>
      cases y with
      | mk socketSite' kind' requestedSupply' gateLocality' transport' route'
          provenance' nameCert' =>
          cases hfields
          rfl

instance socketKindClassifierBHistCarrier :
    BHistCarrier SocketKindClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := socketKindClassifierToEventFlow
  fromEventFlow := socketKindClassifierFromEventFlow

instance socketKindClassifierChapterTasteGate :
    ChapterTasteGate SocketKindClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change socketKindClassifierFromEventFlow (socketKindClassifierToEventFlow x) = some x
    exact socketKindClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (socketKindClassifierToEventFlow_injective heq)

instance socketKindClassifierFieldFaithful :
    FieldFaithful SocketKindClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := socketKindClassifierFields
  field_faithful := socketKindClassifier_field_faithful

instance socketKindClassifierNontrivial :
    Nontrivial SocketKindClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SocketKindClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SocketKindClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SocketKindClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  socketKindClassifierChapterTasteGate

theorem SocketKindClassifierTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SocketKindClassifierUp) ∧
      Nonempty (FieldFaithful SocketKindClassifierUp) ∧
      Nonempty (Nontrivial SocketKindClassifierUp) ∧
        (∀ h : BHist,
          socketKindClassifierDecodeBHist (socketKindClassifierEncodeBHist h) = h) ∧
          socketKindClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨socketKindClassifierChapterTasteGate⟩, ⟨socketKindClassifierFieldFaithful⟩,
      ⟨socketKindClassifierNontrivial⟩, socketKindClassifier_decode_encode_bhist, rfl⟩

end BEDC.Derived.SocketKindClassifierUp
