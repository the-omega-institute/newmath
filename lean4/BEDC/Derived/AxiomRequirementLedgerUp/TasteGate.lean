import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxiomRequirementLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxiomRequirementLedgerUp : Type where
  | mk :
      (claim mode witness required refusal transport route provenance componentRoutes
        consumerRoutes package localName : BHist) →
        AxiomRequirementLedgerUp
  deriving DecidableEq

def axiomRequirementLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axiomRequirementLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axiomRequirementLedgerEncodeBHist h

def axiomRequirementLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axiomRequirementLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axiomRequirementLedgerDecodeBHist tail)

private theorem axiomRequirementLedgerDecode_encode_bhist :
    ∀ h : BHist,
      axiomRequirementLedgerDecodeBHist (axiomRequirementLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem axiomRequirementLedger_mk_congr
    {claim claim' mode mode' witness witness' required required' refusal refusal'
      transport transport' route route' provenance provenance' componentRoutes componentRoutes'
      consumerRoutes consumerRoutes' package package' localName localName' : BHist}
    (hClaim : claim' = claim)
    (hMode : mode' = mode)
    (hWitness : witness' = witness)
    (hRequired : required' = required)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hComponentRoutes : componentRoutes' = componentRoutes)
    (hConsumerRoutes : consumerRoutes' = consumerRoutes)
    (hPackage : package' = package)
    (hLocalName : localName' = localName) :
    AxiomRequirementLedgerUp.mk claim' mode' witness' required' refusal' transport' route'
        provenance' componentRoutes' consumerRoutes' package' localName' =
      AxiomRequirementLedgerUp.mk claim mode witness required refusal transport route
        provenance componentRoutes consumerRoutes package localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hClaim
  cases hMode
  cases hWitness
  cases hRequired
  cases hRefusal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hComponentRoutes
  cases hConsumerRoutes
  cases hPackage
  cases hLocalName
  rfl

def axiomRequirementLedgerToEventFlow : AxiomRequirementLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxiomRequirementLedgerUp.mk claim mode witness required refusal transport route provenance
      componentRoutes consumerRoutes package localName =>
      [[BMark.b0],
        axiomRequirementLedgerEncodeBHist claim,
        [BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist mode,
        [BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist required,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axiomRequirementLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist componentRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist consumerRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRequirementLedgerEncodeBHist localName]

def axiomRequirementLedgerFromEventFlow :
    EventFlow → Option AxiomRequirementLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | claim :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | mode :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | witness :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | required :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
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
                                                                      | componentRoutes ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | consumerRoutes ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | package ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | localName ::
                                                                                                  rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (AxiomRequirementLedgerUp.mk
                                                                                                          (axiomRequirementLedgerDecodeBHist claim)
                                                                                                          (axiomRequirementLedgerDecodeBHist mode)
                                                                                                          (axiomRequirementLedgerDecodeBHist witness)
                                                                                                          (axiomRequirementLedgerDecodeBHist required)
                                                                                                          (axiomRequirementLedgerDecodeBHist refusal)
                                                                                                          (axiomRequirementLedgerDecodeBHist transport)
                                                                                                          (axiomRequirementLedgerDecodeBHist route)
                                                                                                          (axiomRequirementLedgerDecodeBHist provenance)
                                                                                                          (axiomRequirementLedgerDecodeBHist componentRoutes)
                                                                                                          (axiomRequirementLedgerDecodeBHist consumerRoutes)
                                                                                                          (axiomRequirementLedgerDecodeBHist package)
                                                                                                          (axiomRequirementLedgerDecodeBHist localName))
                                                                                                  | _ :: _ => none

private theorem axiomRequirementLedger_round_trip :
    ∀ x : AxiomRequirementLedgerUp,
      axiomRequirementLedgerFromEventFlow
        (axiomRequirementLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk claim mode witness required refusal transport route provenance componentRoutes
      consumerRoutes package localName =>
      change
        some
          (AxiomRequirementLedgerUp.mk
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist claim))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist mode))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist witness))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist required))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist refusal))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist transport))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist route))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist provenance))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist componentRoutes))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist consumerRoutes))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist package))
            (axiomRequirementLedgerDecodeBHist
              (axiomRequirementLedgerEncodeBHist localName))) =
          some
            (AxiomRequirementLedgerUp.mk claim mode witness required refusal transport route
              provenance componentRoutes consumerRoutes package localName)
      exact
        congrArg some
          (axiomRequirementLedger_mk_congr
            (axiomRequirementLedgerDecode_encode_bhist claim)
            (axiomRequirementLedgerDecode_encode_bhist mode)
            (axiomRequirementLedgerDecode_encode_bhist witness)
            (axiomRequirementLedgerDecode_encode_bhist required)
            (axiomRequirementLedgerDecode_encode_bhist refusal)
            (axiomRequirementLedgerDecode_encode_bhist transport)
            (axiomRequirementLedgerDecode_encode_bhist route)
            (axiomRequirementLedgerDecode_encode_bhist provenance)
            (axiomRequirementLedgerDecode_encode_bhist componentRoutes)
            (axiomRequirementLedgerDecode_encode_bhist consumerRoutes)
            (axiomRequirementLedgerDecode_encode_bhist package)
            (axiomRequirementLedgerDecode_encode_bhist localName))

private theorem axiomRequirementLedgerToEventFlow_injective
    {x y : AxiomRequirementLedgerUp} :
    axiomRequirementLedgerToEventFlow x = axiomRequirementLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axiomRequirementLedgerFromEventFlow (axiomRequirementLedgerToEventFlow x) =
        axiomRequirementLedgerFromEventFlow (axiomRequirementLedgerToEventFlow y) :=
    congrArg axiomRequirementLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axiomRequirementLedger_round_trip x).symm
      (Eq.trans hread (axiomRequirementLedger_round_trip y)))

instance axiomRequirementLedgerBHistCarrier :
    BHistCarrier AxiomRequirementLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axiomRequirementLedgerToEventFlow
  fromEventFlow := axiomRequirementLedgerFromEventFlow

instance axiomRequirementLedgerChapterTasteGate :
    ChapterTasteGate AxiomRequirementLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      axiomRequirementLedgerFromEventFlow (axiomRequirementLedgerToEventFlow x) =
        some x
    exact axiomRequirementLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axiomRequirementLedgerToEventFlow_injective heq)

def axiomRequirementLedgerFields : AxiomRequirementLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxiomRequirementLedgerUp.mk claim mode witness required refusal transport route provenance
      componentRoutes consumerRoutes package localName =>
      [claim, mode, witness, required, refusal, transport, route, provenance, componentRoutes,
        consumerRoutes, package, localName]

private theorem axiomRequirementLedger_field_faithful_concrete :
    ∀ x y : AxiomRequirementLedgerUp,
      axiomRequirementLedgerFields x = axiomRequirementLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk claim mode witness required refusal transport route provenance componentRoutes
      consumerRoutes package localName =>
      cases y with
      | mk claim' mode' witness' required' refusal' transport' route' provenance'
          componentRoutes' consumerRoutes' package' localName' =>
          change
            [claim, mode, witness, required, refusal, transport, route, provenance,
                componentRoutes, consumerRoutes, package, localName] =
              [claim', mode', witness', required', refusal', transport', route', provenance',
                componentRoutes', consumerRoutes', package', localName'] at hfields
          injection hfields with hClaim hTail0
          injection hTail0 with hMode hTail1
          injection hTail1 with hWitness hTail2
          injection hTail2 with hRequired hTail3
          injection hTail3 with hRefusal hTail4
          injection hTail4 with hTransport hTail5
          injection hTail5 with hRoute hTail6
          injection hTail6 with hProvenance hTail7
          injection hTail7 with hComponentRoutes hTail8
          injection hTail8 with hConsumerRoutes hTail9
          injection hTail9 with hPackage hTail10
          injection hTail10 with hLocalName _hNil
          cases hClaim
          cases hMode
          cases hWitness
          cases hRequired
          cases hRefusal
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hComponentRoutes
          cases hConsumerRoutes
          cases hPackage
          cases hLocalName
          rfl

instance axiomRequirementLedgerFieldFaithful :
    FieldFaithful AxiomRequirementLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := axiomRequirementLedgerFields
  field_faithful := axiomRequirementLedger_field_faithful_concrete

theorem AxiomRequirementLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      axiomRequirementLedgerDecodeBHist (axiomRequirementLedgerEncodeBHist h) = h) /\
      (forall x : AxiomRequirementLedgerUp,
        axiomRequirementLedgerFromEventFlow
          (axiomRequirementLedgerToEventFlow x) = some x) /\
      (forall x y : AxiomRequirementLedgerUp,
        axiomRequirementLedgerToEventFlow x = axiomRequirementLedgerToEventFlow y ->
          x = y) /\
      axiomRequirementLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact axiomRequirementLedgerDecode_encode_bhist
  · constructor
    · exact axiomRequirementLedger_round_trip
    · constructor
      · intro x y heq
        exact axiomRequirementLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AxiomRequirementLedgerUp
