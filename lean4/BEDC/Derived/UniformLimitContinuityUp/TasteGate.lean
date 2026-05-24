import BEDC.Derived.UniformLimitContinuityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def uniformLimitContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitContinuityEncodeBHist h

def uniformLimitContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitContinuityDecodeBHist tail)

private theorem uniformLimitContinuity_decode_encode_bhist :
    ∀ h : BHist,
      uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem uniformLimitContinuity_mk_congr
    {family family' sharedModulus sharedModulus' tailLedger tailLedger'
      regularHandoff regularHandoff' realSeal realSeal' continuousGraph continuousGraph'
      uniformConsumer uniformConsumer' transport transport' replay replay'
      provenance provenance' localName localName' : BHist}
    (hFamily : family' = family)
    (hSharedModulus : sharedModulus' = sharedModulus)
    (hTailLedger : tailLedger' = tailLedger)
    (hRegularHandoff : regularHandoff' = regularHandoff)
    (hRealSeal : realSeal' = realSeal)
    (hContinuousGraph : continuousGraph' = continuousGraph)
    (hUniformConsumer : uniformConsumer' = uniformConsumer)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    BEDC.Derived.UniformLimitContinuityUp.mk family' sharedModulus' tailLedger' regularHandoff'
        realSeal' continuousGraph' uniformConsumer' transport' replay' provenance' localName' =
      BEDC.Derived.UniformLimitContinuityUp.mk family sharedModulus tailLedger regularHandoff realSeal
        continuousGraph uniformConsumer transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFamily
  cases hSharedModulus
  cases hTailLedger
  cases hRegularHandoff
  cases hRealSeal
  cases hContinuousGraph
  cases hUniformConsumer
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def uniformLimitContinuityFields : BEDC.Derived.UniformLimitContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.UniformLimitContinuityUp.mk family sharedModulus tailLedger regularHandoff realSeal
      continuousGraph uniformConsumer transport replay provenance localName =>
      [family, sharedModulus, tailLedger, regularHandoff, realSeal, continuousGraph,
        uniformConsumer, transport, replay, provenance, localName]

def uniformLimitContinuityToEventFlow : BEDC.Derived.UniformLimitContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.UniformLimitContinuityUp.mk family sharedModulus tailLedger regularHandoff realSeal
      continuousGraph uniformConsumer transport replay provenance localName =>
      [uniformLimitContinuityEncodeBHist family,
        uniformLimitContinuityEncodeBHist sharedModulus,
        uniformLimitContinuityEncodeBHist tailLedger,
        uniformLimitContinuityEncodeBHist regularHandoff,
        uniformLimitContinuityEncodeBHist realSeal,
        uniformLimitContinuityEncodeBHist continuousGraph,
        uniformLimitContinuityEncodeBHist uniformConsumer,
        uniformLimitContinuityEncodeBHist transport,
        uniformLimitContinuityEncodeBHist replay,
        uniformLimitContinuityEncodeBHist provenance,
        uniformLimitContinuityEncodeBHist localName]

def uniformLimitContinuityFromEventFlow : EventFlow → Option BEDC.Derived.UniformLimitContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | family :: rest0 =>
      match rest0 with
      | [] => none
      | sharedModulus :: rest1 =>
          match rest1 with
          | [] => none
          | tailLedger :: rest2 =>
              match rest2 with
              | [] => none
              | regularHandoff :: rest3 =>
                  match rest3 with
                  | [] => none
                  | realSeal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | continuousGraph :: rest5 =>
                          match rest5 with
                          | [] => none
                          | uniformConsumer :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (BEDC.Derived.UniformLimitContinuityUp.mk
                                                      (uniformLimitContinuityDecodeBHist family)
                                                      (uniformLimitContinuityDecodeBHist
                                                        sharedModulus)
                                                      (uniformLimitContinuityDecodeBHist
                                                        tailLedger)
                                                      (uniformLimitContinuityDecodeBHist
                                                        regularHandoff)
                                                      (uniformLimitContinuityDecodeBHist realSeal)
                                                      (uniformLimitContinuityDecodeBHist
                                                        continuousGraph)
                                                      (uniformLimitContinuityDecodeBHist
                                                        uniformConsumer)
                                                      (uniformLimitContinuityDecodeBHist transport)
                                                      (uniformLimitContinuityDecodeBHist replay)
                                                      (uniformLimitContinuityDecodeBHist provenance)
                                                      (uniformLimitContinuityDecodeBHist localName))
                                              | _ :: _ => none

private theorem uniformLimitContinuity_round_trip :
    ∀ x : BEDC.Derived.UniformLimitContinuityUp,
      uniformLimitContinuityFromEventFlow (uniformLimitContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family sharedModulus tailLedger regularHandoff realSeal continuousGraph uniformConsumer
      transport replay provenance localName =>
      change
        some
          (BEDC.Derived.UniformLimitContinuityUp.mk
            (uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist family))
            (uniformLimitContinuityDecodeBHist
              (uniformLimitContinuityEncodeBHist sharedModulus))
            (uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist tailLedger))
            (uniformLimitContinuityDecodeBHist
              (uniformLimitContinuityEncodeBHist regularHandoff))
            (uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist realSeal))
            (uniformLimitContinuityDecodeBHist
              (uniformLimitContinuityEncodeBHist continuousGraph))
            (uniformLimitContinuityDecodeBHist
              (uniformLimitContinuityEncodeBHist uniformConsumer))
            (uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist transport))
            (uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist replay))
            (uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist provenance))
            (uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist localName))) =
          some
            (BEDC.Derived.UniformLimitContinuityUp.mk family sharedModulus tailLedger regularHandoff
              realSeal continuousGraph uniformConsumer transport replay provenance localName)
      exact
        congrArg some
          (uniformLimitContinuity_mk_congr
            (uniformLimitContinuity_decode_encode_bhist family)
            (uniformLimitContinuity_decode_encode_bhist sharedModulus)
            (uniformLimitContinuity_decode_encode_bhist tailLedger)
            (uniformLimitContinuity_decode_encode_bhist regularHandoff)
            (uniformLimitContinuity_decode_encode_bhist realSeal)
            (uniformLimitContinuity_decode_encode_bhist continuousGraph)
            (uniformLimitContinuity_decode_encode_bhist uniformConsumer)
            (uniformLimitContinuity_decode_encode_bhist transport)
            (uniformLimitContinuity_decode_encode_bhist replay)
            (uniformLimitContinuity_decode_encode_bhist provenance)
            (uniformLimitContinuity_decode_encode_bhist localName))

private theorem uniformLimitContinuityToEventFlow_injective
    {x y : UniformLimitContinuityUp} :
    uniformLimitContinuityToEventFlow x = uniformLimitContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitContinuityFromEventFlow (uniformLimitContinuityToEventFlow x) =
        uniformLimitContinuityFromEventFlow (uniformLimitContinuityToEventFlow y) :=
    congrArg uniformLimitContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformLimitContinuity_round_trip x).symm
      (Eq.trans hread (uniformLimitContinuity_round_trip y)))

private theorem uniformLimitContinuity_field_faithful :
    ∀ x y : BEDC.Derived.UniformLimitContinuityUp,
      uniformLimitContinuityFields x = uniformLimitContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk family₁ sharedModulus₁ tailLedger₁ regularHandoff₁ realSeal₁ continuousGraph₁
      uniformConsumer₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk family₂ sharedModulus₂ tailLedger₂ regularHandoff₂ realSeal₂ continuousGraph₂
          uniformConsumer₂ transport₂ replay₂ provenance₂ localName₂ =>
          injection h with hFamily t1
          injection t1 with hSharedModulus t2
          injection t2 with hTailLedger t3
          injection t3 with hRegularHandoff t4
          injection t4 with hRealSeal t5
          injection t5 with hContinuousGraph t6
          injection t6 with hUniformConsumer t7
          injection t7 with hTransport t8
          injection t8 with hReplay t9
          injection t9 with hProvenance t10
          injection t10 with hLocalName _
          subst hFamily
          subst hSharedModulus
          subst hTailLedger
          subst hRegularHandoff
          subst hRealSeal
          subst hContinuousGraph
          subst hUniformConsumer
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance uniformLimitContinuityBHistCarrier : BHistCarrier BEDC.Derived.UniformLimitContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitContinuityToEventFlow
  fromEventFlow := uniformLimitContinuityFromEventFlow

instance uniformLimitContinuityChapterTasteGate : ChapterTasteGate BEDC.Derived.UniformLimitContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLimitContinuityFromEventFlow (uniformLimitContinuityToEventFlow x) = some x
    exact uniformLimitContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLimitContinuityToEventFlow_injective heq)

instance uniformLimitContinuityFieldFaithful : FieldFaithful BEDC.Derived.UniformLimitContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitContinuityFields
  field_faithful := uniformLimitContinuity_field_faithful

instance uniformLimitContinuityNontrivial : Nontrivial BEDC.Derived.UniformLimitContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.UniformLimitContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BEDC.Derived.UniformLimitContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.UniformLimitContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitContinuityChapterTasteGate

theorem UniformLimitContinuityUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformLimitContinuityDecodeBHist (uniformLimitContinuityEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.UniformLimitContinuityUp,
        uniformLimitContinuityFromEventFlow (uniformLimitContinuityToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.UniformLimitContinuityUp,
          uniformLimitContinuityToEventFlow x = uniformLimitContinuityToEventFlow y → x = y) ∧
          uniformLimitContinuityEncodeBHist BHist.Empty = ([] : List BMark) :=
  -- BEDC touchpoint anchor: BHist BMark
  ⟨uniformLimitContinuity_decode_encode_bhist,
    ⟨uniformLimitContinuity_round_trip,
      ⟨fun _x _y heq => uniformLimitContinuityToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.UniformLimitContinuityUp
