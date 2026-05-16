import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CookFrontierWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CookFrontierWitnessUp : Type where
  | mk :
      (frontier tmToTag tagToCyclic cyclicToRule110 haltedTarget replayAudit obstruction
        transport continuation provenance name : BHist) →
      CookFrontierWitnessUp
  deriving DecidableEq

def cookFrontierWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cookFrontierWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cookFrontierWitnessEncodeBHist h

def cookFrontierWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cookFrontierWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cookFrontierWitnessDecodeBHist tail)

private theorem cookFrontierWitnessDecode_encode_bhist :
    ∀ h : BHist, cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cookFrontierWitness_mk_congr
    {frontier frontier' tmToTag tmToTag' tagToCyclic tagToCyclic'
      cyclicToRule110 cyclicToRule110' haltedTarget haltedTarget' replayAudit replayAudit'
      obstruction obstruction' transport transport' continuation continuation'
      provenance provenance' name name' : BHist}
    (hFrontier : frontier' = frontier)
    (hTmToTag : tmToTag' = tmToTag)
    (hTagToCyclic : tagToCyclic' = tagToCyclic)
    (hCyclicToRule110 : cyclicToRule110' = cyclicToRule110)
    (hHaltedTarget : haltedTarget' = haltedTarget)
    (hReplayAudit : replayAudit' = replayAudit)
    (hObstruction : obstruction' = obstruction)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CookFrontierWitnessUp.mk frontier' tmToTag' tagToCyclic' cyclicToRule110'
        haltedTarget' replayAudit' obstruction' transport' continuation' provenance' name' =
      CookFrontierWitnessUp.mk frontier tmToTag tagToCyclic cyclicToRule110 haltedTarget
        replayAudit obstruction transport continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFrontier
  cases hTmToTag
  cases hTagToCyclic
  cases hCyclicToRule110
  cases hHaltedTarget
  cases hReplayAudit
  cases hObstruction
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def cookFrontierWitnessFields : CookFrontierWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CookFrontierWitnessUp.mk frontier tmToTag tagToCyclic cyclicToRule110 haltedTarget
      replayAudit obstruction transport continuation provenance name =>
      [frontier, tmToTag, tagToCyclic, cyclicToRule110, haltedTarget, replayAudit, obstruction,
        transport, continuation, provenance, name]

def cookFrontierWitnessToEventFlow : CookFrontierWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cookFrontierWitnessFields x).map cookFrontierWitnessEncodeBHist

private def cookFrontierWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cookFrontierWitnessEventAtDefault index rest

def cookFrontierWitnessFromEventFlow (ef : EventFlow) : Option CookFrontierWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CookFrontierWitnessUp.mk
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 0 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 1 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 2 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 3 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 4 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 5 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 6 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 7 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 8 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 9 ef))
      (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEventAtDefault 10 ef)))

private theorem cookFrontierWitness_round_trip :
    ∀ x : CookFrontierWitnessUp,
      cookFrontierWitnessFromEventFlow (cookFrontierWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk frontier tmToTag tagToCyclic cyclicToRule110 haltedTarget replayAudit obstruction
      transport continuation provenance name =>
      change
        some
          (CookFrontierWitnessUp.mk
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist frontier))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist tmToTag))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist tagToCyclic))
            (cookFrontierWitnessDecodeBHist
              (cookFrontierWitnessEncodeBHist cyclicToRule110))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist haltedTarget))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist replayAudit))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist obstruction))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist transport))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist continuation))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist provenance))
            (cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist name))) =
          some
            (CookFrontierWitnessUp.mk frontier tmToTag tagToCyclic cyclicToRule110
              haltedTarget replayAudit obstruction transport continuation provenance name)
      exact
        congrArg some
          (cookFrontierWitness_mk_congr
            (cookFrontierWitnessDecode_encode_bhist frontier)
            (cookFrontierWitnessDecode_encode_bhist tmToTag)
            (cookFrontierWitnessDecode_encode_bhist tagToCyclic)
            (cookFrontierWitnessDecode_encode_bhist cyclicToRule110)
            (cookFrontierWitnessDecode_encode_bhist haltedTarget)
            (cookFrontierWitnessDecode_encode_bhist replayAudit)
            (cookFrontierWitnessDecode_encode_bhist obstruction)
            (cookFrontierWitnessDecode_encode_bhist transport)
            (cookFrontierWitnessDecode_encode_bhist continuation)
            (cookFrontierWitnessDecode_encode_bhist provenance)
            (cookFrontierWitnessDecode_encode_bhist name))

private theorem cookFrontierWitnessToEventFlow_injective {x y : CookFrontierWitnessUp} :
    cookFrontierWitnessToEventFlow x = cookFrontierWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cookFrontierWitnessFromEventFlow (cookFrontierWitnessToEventFlow x) =
        cookFrontierWitnessFromEventFlow (cookFrontierWitnessToEventFlow y) :=
    congrArg cookFrontierWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cookFrontierWitness_round_trip x).symm
      (Eq.trans hread (cookFrontierWitness_round_trip y)))

private theorem cookFrontierWitness_fields_faithful :
    ∀ x y : CookFrontierWitnessUp,
      cookFrontierWitnessFields x = cookFrontierWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk frontier₁ tmToTag₁ tagToCyclic₁ cyclicToRule110₁ haltedTarget₁ replayAudit₁
      obstruction₁ transport₁ continuation₁ provenance₁ name₁ =>
      cases y with
      | mk frontier₂ tmToTag₂ tagToCyclic₂ cyclicToRule110₂ haltedTarget₂ replayAudit₂
          obstruction₂ transport₂ continuation₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance cookFrontierWitnessBHistCarrier : BHistCarrier CookFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cookFrontierWitnessToEventFlow
  fromEventFlow := cookFrontierWitnessFromEventFlow

instance cookFrontierWitnessChapterTasteGate :
    ChapterTasteGate CookFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cookFrontierWitnessFromEventFlow (cookFrontierWitnessToEventFlow x) = some x
    exact cookFrontierWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cookFrontierWitnessToEventFlow_injective heq)

instance cookFrontierWitnessFieldFaithful : FieldFaithful CookFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cookFrontierWitnessFields
  field_faithful := cookFrontierWitness_fields_faithful

instance cookFrontierWitnessNontrivial : Nontrivial CookFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CookFrontierWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CookFrontierWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CookFrontierWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cookFrontierWitnessChapterTasteGate

theorem CookFrontierWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, cookFrontierWitnessDecodeBHist (cookFrontierWitnessEncodeBHist h) = h) ∧
      (∀ x : CookFrontierWitnessUp,
        cookFrontierWitnessFromEventFlow (cookFrontierWitnessToEventFlow x) = some x) ∧
        (∀ x y : CookFrontierWitnessUp,
          cookFrontierWitnessToEventFlow x = cookFrontierWitnessToEventFlow y → x = y) ∧
          cookFrontierWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cookFrontierWitnessDecode_encode_bhist
  · constructor
    · exact cookFrontierWitness_round_trip
    · constructor
      · intro x y heq
        exact cookFrontierWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.CookFrontierWitnessUp
