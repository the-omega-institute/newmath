import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapConcreteInventoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapConcreteInventoryUp : Type where
  | mk :
      (map established conditional obstruction frontier consumer transport route provenance
        name : BHist) →
      AuditMapConcreteInventoryUp

def auditMapConcreteInventoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapConcreteInventoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapConcreteInventoryEncodeBHist h

def auditMapConcreteInventoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapConcreteInventoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapConcreteInventoryDecodeBHist tail)

private theorem auditMapConcreteInventoryDecode_encode_bhist :
    ∀ h : BHist,
      auditMapConcreteInventoryDecodeBHist
          (auditMapConcreteInventoryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem auditMapConcreteInventory_mk_congr
    {map map' established established' conditional conditional' obstruction obstruction'
      frontier frontier' consumer consumer' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hMap : map' = map)
    (hEstablished : established' = established)
    (hConditional : conditional' = conditional)
    (hObstruction : obstruction' = obstruction)
    (hFrontier : frontier' = frontier)
    (hConsumer : consumer' = consumer)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    AuditMapConcreteInventoryUp.mk map' established' conditional' obstruction' frontier'
        consumer' transport' route' provenance' name' =
      AuditMapConcreteInventoryUp.mk map established conditional obstruction frontier consumer
        transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMap
  cases hEstablished
  cases hConditional
  cases hObstruction
  cases hFrontier
  cases hConsumer
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def auditMapConcreteInventoryToEventFlow :
    AuditMapConcreteInventoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapConcreteInventoryUp.mk map established conditional obstruction frontier consumer
      transport route provenance name =>
      [[BMark.b0],
        auditMapConcreteInventoryEncodeBHist map,
        [BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist established,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist conditional,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapConcreteInventoryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapConcreteInventoryEncodeBHist name]

def auditMapConcreteInventoryFromEventFlow :
    EventFlow → Option AuditMapConcreteInventoryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | map :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | established :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | conditional :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | obstruction :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | frontier :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | consumer :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (AuditMapConcreteInventoryUp.mk
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            map)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            established)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            conditional)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            obstruction)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            frontier)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            consumer)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            transport)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            route)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            provenance)
                                                                                          (auditMapConcreteInventoryDecodeBHist
                                                                                            name))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem auditMapConcreteInventory_round_trip :
    ∀ x : AuditMapConcreteInventoryUp,
      auditMapConcreteInventoryFromEventFlow
          (auditMapConcreteInventoryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk map established conditional obstruction frontier consumer transport route provenance
      name =>
      change
        some
          (AuditMapConcreteInventoryUp.mk
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist map))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist established))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist conditional))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist obstruction))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist frontier))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist consumer))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist transport))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist route))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist provenance))
            (auditMapConcreteInventoryDecodeBHist
              (auditMapConcreteInventoryEncodeBHist name))) =
          some
            (AuditMapConcreteInventoryUp.mk map established conditional obstruction frontier
              consumer transport route provenance name)
      exact
        congrArg some
          (auditMapConcreteInventory_mk_congr
            (auditMapConcreteInventoryDecode_encode_bhist map)
            (auditMapConcreteInventoryDecode_encode_bhist established)
            (auditMapConcreteInventoryDecode_encode_bhist conditional)
            (auditMapConcreteInventoryDecode_encode_bhist obstruction)
            (auditMapConcreteInventoryDecode_encode_bhist frontier)
            (auditMapConcreteInventoryDecode_encode_bhist consumer)
            (auditMapConcreteInventoryDecode_encode_bhist transport)
            (auditMapConcreteInventoryDecode_encode_bhist route)
            (auditMapConcreteInventoryDecode_encode_bhist provenance)
            (auditMapConcreteInventoryDecode_encode_bhist name))

private theorem auditMapConcreteInventoryToEventFlow_injective
    {x y : AuditMapConcreteInventoryUp} :
    auditMapConcreteInventoryToEventFlow x =
        auditMapConcreteInventoryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapConcreteInventoryFromEventFlow
          (auditMapConcreteInventoryToEventFlow x) =
        auditMapConcreteInventoryFromEventFlow
          (auditMapConcreteInventoryToEventFlow y) :=
    congrArg auditMapConcreteInventoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapConcreteInventory_round_trip x).symm
      (Eq.trans hread (auditMapConcreteInventory_round_trip y)))

instance auditMapConcreteInventoryBHistCarrier :
    BHistCarrier AuditMapConcreteInventoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapConcreteInventoryToEventFlow
  fromEventFlow := auditMapConcreteInventoryFromEventFlow

instance auditMapConcreteInventoryChapterTasteGate :
    ChapterTasteGate AuditMapConcreteInventoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      auditMapConcreteInventoryFromEventFlow
          (auditMapConcreteInventoryToEventFlow x) =
        some x
    exact auditMapConcreteInventory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapConcreteInventoryToEventFlow_injective heq)

instance auditMapConcreteInventoryFieldFaithful :
    FieldFaithful AuditMapConcreteInventoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AuditMapConcreteInventoryUp.mk map established conditional obstruction frontier consumer
        transport route provenance name =>
        [map, established, conditional, obstruction, frontier, consumer, transport, route,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk map1 established1 conditional1 obstruction1 frontier1 consumer1 transport1 route1
        provenance1 name1 =>
        cases y with
        | mk map2 established2 conditional2 obstruction2 frontier2 consumer2 transport2 route2
            provenance2 name2 =>
            injection h with hMap t1
            injection t1 with hEstablished t2
            injection t2 with hConditional t3
            injection t3 with hObstruction t4
            injection t4 with hFrontier t5
            injection t5 with hConsumer t6
            injection t6 with hTransport t7
            injection t7 with hRoute t8
            injection t8 with hProvenance t9
            injection t9 with hName _
            cases hMap
            cases hEstablished
            cases hConditional
            cases hObstruction
            cases hFrontier
            cases hConsumer
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

theorem AuditMapConcreteInventoryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapConcreteInventoryDecodeBHist
          (auditMapConcreteInventoryEncodeBHist h) =
        h) ∧
      (∀ x : AuditMapConcreteInventoryUp,
        auditMapConcreteInventoryFromEventFlow
            (auditMapConcreteInventoryToEventFlow x) =
          some x) ∧
        (∀ x y : AuditMapConcreteInventoryUp,
          auditMapConcreteInventoryToEventFlow x =
              auditMapConcreteInventoryToEventFlow y →
            x = y) ∧
          auditMapConcreteInventoryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapConcreteInventoryDecode_encode_bhist
  · constructor
    · exact auditMapConcreteInventory_round_trip
    · constructor
      · intro x y heq
        exact auditMapConcreteInventoryToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditMapConcreteInventoryUp
