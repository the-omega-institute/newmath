import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AtsujiSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AtsujiSpaceUp : Type where
  | mk :
      (metric continuousMap uniformModulus compactMetric realSeal transport route
        provenance localName : BHist) →
      AtsujiSpaceUp
  deriving DecidableEq

private def atsujiSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: atsujiSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: atsujiSpaceEncodeBHist h

private def atsujiSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (atsujiSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (atsujiSpaceDecodeBHist tail)

private theorem atsujiSpaceDecode_encode_bhist :
    ∀ h : BHist, atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem atsujiSpace_mk_congr
    {metric metric' continuousMap continuousMap' uniformModulus uniformModulus'
      compactMetric compactMetric' realSeal realSeal' transport transport' route route'
      provenance provenance' localName localName' : BHist}
    (hMetric : metric' = metric)
    (hContinuousMap : continuousMap' = continuousMap)
    (hUniformModulus : uniformModulus' = uniformModulus)
    (hCompactMetric : compactMetric' = compactMetric)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    AtsujiSpaceUp.mk metric' continuousMap' uniformModulus' compactMetric' realSeal'
        transport' route' provenance' localName' =
      AtsujiSpaceUp.mk metric continuousMap uniformModulus compactMetric realSeal
        transport route provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMetric
  cases hContinuousMap
  cases hUniformModulus
  cases hCompactMetric
  cases hRealSeal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hLocalName
  rfl

private def atsujiSpaceToEventFlow : AtsujiSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AtsujiSpaceUp.mk metric continuousMap uniformModulus compactMetric realSeal
      transport route provenance localName =>
      [[BMark.b0],
        atsujiSpaceEncodeBHist metric,
        [BMark.b1, BMark.b0],
        atsujiSpaceEncodeBHist continuousMap,
        [BMark.b1, BMark.b1, BMark.b0],
        atsujiSpaceEncodeBHist uniformModulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        atsujiSpaceEncodeBHist compactMetric,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        atsujiSpaceEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        atsujiSpaceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        atsujiSpaceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        atsujiSpaceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        atsujiSpaceEncodeBHist localName]

private def atsujiSpaceFromEventFlow : EventFlow → Option AtsujiSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metric :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | continuousMap :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | uniformModulus :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | compactMetric :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
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
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (AtsujiSpaceUp.mk
                                                                                  (atsujiSpaceDecodeBHist metric)
                                                                                  (atsujiSpaceDecodeBHist continuousMap)
                                                                                  (atsujiSpaceDecodeBHist uniformModulus)
                                                                                  (atsujiSpaceDecodeBHist compactMetric)
                                                                                  (atsujiSpaceDecodeBHist realSeal)
                                                                                  (atsujiSpaceDecodeBHist transport)
                                                                                  (atsujiSpaceDecodeBHist route)
                                                                                  (atsujiSpaceDecodeBHist provenance)
                                                                                  (atsujiSpaceDecodeBHist localName))
                                                                          | _ :: _ => none

private theorem atsujiSpace_round_trip :
    ∀ x : AtsujiSpaceUp,
      atsujiSpaceFromEventFlow (atsujiSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric continuousMap uniformModulus compactMetric realSeal transport route
      provenance localName =>
      change
        some
          (AtsujiSpaceUp.mk
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist metric))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist continuousMap))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist uniformModulus))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist compactMetric))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist realSeal))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist transport))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist route))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist provenance))
            (atsujiSpaceDecodeBHist (atsujiSpaceEncodeBHist localName))) =
          some
            (AtsujiSpaceUp.mk metric continuousMap uniformModulus compactMetric realSeal
              transport route provenance localName)
      exact
        congrArg some
          (atsujiSpace_mk_congr
            (atsujiSpaceDecode_encode_bhist metric)
            (atsujiSpaceDecode_encode_bhist continuousMap)
            (atsujiSpaceDecode_encode_bhist uniformModulus)
            (atsujiSpaceDecode_encode_bhist compactMetric)
            (atsujiSpaceDecode_encode_bhist realSeal)
            (atsujiSpaceDecode_encode_bhist transport)
            (atsujiSpaceDecode_encode_bhist route)
            (atsujiSpaceDecode_encode_bhist provenance)
            (atsujiSpaceDecode_encode_bhist localName))

private theorem atsujiSpaceToEventFlow_injective {x y : AtsujiSpaceUp} :
    atsujiSpaceToEventFlow x = atsujiSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      atsujiSpaceFromEventFlow (atsujiSpaceToEventFlow x) =
        atsujiSpaceFromEventFlow (atsujiSpaceToEventFlow y) :=
    congrArg atsujiSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (atsujiSpace_round_trip x).symm
      (Eq.trans hread (atsujiSpace_round_trip y)))

instance atsujiSpaceBHistCarrier : BHistCarrier AtsujiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := atsujiSpaceToEventFlow
  fromEventFlow := atsujiSpaceFromEventFlow

instance atsujiSpaceChapterTasteGate : ChapterTasteGate AtsujiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change atsujiSpaceFromEventFlow (atsujiSpaceToEventFlow x) = some x
    exact atsujiSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (atsujiSpaceToEventFlow_injective heq)

instance atsujiSpaceFieldFaithful : FieldFaithful AtsujiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AtsujiSpaceUp.mk metric continuousMap uniformModulus compactMetric realSeal
        transport route provenance localName =>
        [metric, continuousMap, uniformModulus, compactMetric, realSeal, transport, route,
          provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk metric₁ continuousMap₁ uniformModulus₁ compactMetric₁ realSeal₁ transport₁
        route₁ provenance₁ localName₁ =>
        cases y with
        | mk metric₂ continuousMap₂ uniformModulus₂ compactMetric₂ realSeal₂ transport₂
            route₂ provenance₂ localName₂ =>
            injection h with hMetric t1
            injection t1 with hContinuousMap t2
            injection t2 with hUniformModulus t3
            injection t3 with hCompactMetric t4
            injection t4 with hRealSeal t5
            injection t5 with hTransport t6
            injection t6 with hRoute t7
            injection t7 with hProvenance t8
            injection t8 with hLocalName _
            cases hMetric
            cases hContinuousMap
            cases hUniformModulus
            cases hCompactMetric
            cases hRealSeal
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hLocalName
            rfl

instance atsujiSpaceNontrivial : Nontrivial AtsujiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AtsujiSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AtsujiSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AtsujiSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AtsujiSpaceUp) ∧
      Nonempty (FieldFaithful AtsujiSpaceUp) ∧
        Nonempty (Nontrivial AtsujiSpaceUp) ∧
          atsujiSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨atsujiSpaceChapterTasteGate⟩
  · constructor
    · exact ⟨atsujiSpaceFieldFaithful⟩
    · constructor
      · exact ⟨atsujiSpaceNontrivial⟩
      · rfl

end BEDC.Derived.AtsujiSpaceUp
