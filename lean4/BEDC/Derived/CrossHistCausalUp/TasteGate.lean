import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CrossHistCausalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CrossHistCausalUp : Type where
  | mk :
      (anchorA anchorB slot witness transports probes routes provenance localName : BHist) →
        CrossHistCausalUp
  deriving DecidableEq

private def CrossHistCausalUp_taste_gate_boundary_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CrossHistCausalUp_taste_gate_boundary_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CrossHistCausalUp_taste_gate_boundary_encodeBHist h

private def CrossHistCausalUp_taste_gate_boundary_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CrossHistCausalUp_taste_gate_boundary_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CrossHistCausalUp_taste_gate_boundary_decodeBHist tail)

private theorem CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist :
    ∀ h : BHist,
      CrossHistCausalUp_taste_gate_boundary_decodeBHist
        (CrossHistCausalUp_taste_gate_boundary_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def CrossHistCausalUp_taste_gate_boundary_toEventFlow :
    CrossHistCausalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes provenance
      localName =>
      [[BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist anchorA,
        [BMark.b1, BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist anchorB,
        [BMark.b1, BMark.b1, BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist slot,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist probes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        CrossHistCausalUp_taste_gate_boundary_encodeBHist localName]

private def CrossHistCausalUp_taste_gate_boundary_fromEventFlow :
    EventFlow → Option CrossHistCausalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | anchorA :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | anchorB :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | slot :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | witness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transports :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | probes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
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
                                                                                (CrossHistCausalUp.mk
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    anchorA)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    anchorB)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    slot)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    witness)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    transports)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    probes)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    routes)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    provenance)
                                                                                  (CrossHistCausalUp_taste_gate_boundary_decodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem CrossHistCausalUp_taste_gate_boundary_round_trip :
    ∀ x : CrossHistCausalUp,
      CrossHistCausalUp_taste_gate_boundary_fromEventFlow
        (CrossHistCausalUp_taste_gate_boundary_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk anchorA anchorB slot witness transports probes routes provenance localName =>
      change
        some
          (CrossHistCausalUp.mk
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist anchorA))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist anchorB))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist slot))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist witness))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist transports))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist probes))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist routes))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist provenance))
            (CrossHistCausalUp_taste_gate_boundary_decodeBHist
              (CrossHistCausalUp_taste_gate_boundary_encodeBHist localName))) =
          some
            (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
              provenance localName)
      rw [CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist anchorA,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist anchorB,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist slot,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist witness,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist transports,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist probes,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist routes,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist provenance,
        CrossHistCausalUp_taste_gate_boundary_decode_encode_bhist localName]

private theorem CrossHistCausalUp_taste_gate_boundary_toEventFlow_injective
    {x y : CrossHistCausalUp} :
    CrossHistCausalUp_taste_gate_boundary_toEventFlow x =
      CrossHistCausalUp_taste_gate_boundary_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CrossHistCausalUp_taste_gate_boundary_fromEventFlow
          (CrossHistCausalUp_taste_gate_boundary_toEventFlow x) =
        CrossHistCausalUp_taste_gate_boundary_fromEventFlow
          (CrossHistCausalUp_taste_gate_boundary_toEventFlow y) :=
    congrArg CrossHistCausalUp_taste_gate_boundary_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CrossHistCausalUp_taste_gate_boundary_round_trip x).symm
      (Eq.trans hread (CrossHistCausalUp_taste_gate_boundary_round_trip y)))

instance crossHistCausalBHistCarrier : BHistCarrier CrossHistCausalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CrossHistCausalUp_taste_gate_boundary_toEventFlow
  fromEventFlow := CrossHistCausalUp_taste_gate_boundary_fromEventFlow

instance crossHistCausalChapterTasteGate : ChapterTasteGate CrossHistCausalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CrossHistCausalUp_taste_gate_boundary_fromEventFlow
        (CrossHistCausalUp_taste_gate_boundary_toEventFlow x) = some x
    exact CrossHistCausalUp_taste_gate_boundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CrossHistCausalUp_taste_gate_boundary_toEventFlow_injective heq)

theorem CrossHistCausalUp_taste_gate_boundary :
    (∀ x : CrossHistCausalUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : CrossHistCausalUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact
      ⟨CrossHistCausalUp_taste_gate_boundary_toEventFlow x,
        CrossHistCausalUp_taste_gate_boundary_round_trip x⟩
  · intro x w m hw hm
    exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm

theorem taste_gate :
    (∀ x : CrossHistCausalUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : CrossHistCausalUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) :=
  CrossHistCausalUp_taste_gate_boundary

theorem CrossHistCausalUp_slot_witness_route_transport
    {anchorA anchorB slot slot' witness witness' transports probes routes provenance
      localName : BHist}
    (slotRoute : Cont anchorA slot routes)
    (witnessRoute : Cont anchorB witness probes)
    (sameSlot : hsame slot slot')
    (sameWitness : hsame witness witness') :
    ∃ routes' probes' : BHist,
      Cont anchorA slot' routes' ∧
        Cont anchorB witness' probes' ∧
          hsame routes routes' ∧
            hsame probes probes' ∧
              BHistCarrier.fromEventFlow
                  (BHistCarrier.toEventFlow
                    (CrossHistCausalUp.mk anchorA anchorB slot' witness' transports probes'
                      routes' provenance localName)) =
                some
                  (CrossHistCausalUp.mk anchorA anchorB slot' witness' transports probes'
                    routes' provenance localName) := by
  -- BEDC touchpoint anchor: BHist BMark Cont BHistCarrier
  cases sameSlot
  cases sameWitness
  exact
    ⟨routes, probes, slotRoute, witnessRoute, hsame_refl routes, hsame_refl probes, by
      change
        CrossHistCausalUp_taste_gate_boundary_fromEventFlow
            (CrossHistCausalUp_taste_gate_boundary_toEventFlow
              (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
                provenance localName)) =
          some
            (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
              provenance localName)
      exact
        CrossHistCausalUp_taste_gate_boundary_round_trip
          (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
            provenance localName)⟩

theorem CrossHistCausalUp_slot_locality
    {anchorA anchorB slot witness transports probes routes provenance localName consumer : BHist} :
    UnaryHistory slot →
      UnaryHistory witness →
        Cont slot witness consumer →
          UnaryHistory consumer ∧
            ∃ e : EventFlow,
              BHistCarrier.fromEventFlow e =
                some
                  (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
                    provenance localName) := by
  -- BEDC touchpoint anchor: BHist BMark Cont BHistCarrier
  intro slotUnary witnessUnary slotWitnessConsumer
  constructor
  · exact unary_cont_closed slotUnary witnessUnary slotWitnessConsumer
  · exact
      ⟨CrossHistCausalUp_taste_gate_boundary_toEventFlow
          (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes provenance
            localName),
        by
          change
            CrossHistCausalUp_taste_gate_boundary_fromEventFlow
                (CrossHistCausalUp_taste_gate_boundary_toEventFlow
                  (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
                    provenance localName)) =
              some
                (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
                  provenance localName)
          exact
            CrossHistCausalUp_taste_gate_boundary_round_trip
              (CrossHistCausalUp.mk anchorA anchorB slot witness transports probes routes
                provenance localName)⟩

end BEDC.Derived.CrossHistCausalUp
