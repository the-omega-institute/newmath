import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LayeredRelationGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LayeredRelationGateUp : Type where
  | mk
      (sourceLeft sourceRight layerList preserved notPreserved refusalLedger gateVerdict
        transport continuation provenance : BHist) :
      LayeredRelationGateUp
  deriving DecidableEq

def layeredRelationGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: layeredRelationGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: layeredRelationGateEncodeBHist h

def layeredRelationGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (layeredRelationGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (layeredRelationGateDecodeBHist tail)

private theorem layeredRelationGateDecode_encode_bhist :
    ∀ h : BHist,
      layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def layeredRelationGateToEventFlow : LayeredRelationGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved notPreserved
      refusalLedger gateVerdict transport continuation provenance =>
      [[BMark.b0],
        layeredRelationGateEncodeBHist sourceLeft,
        [BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist sourceRight,
        [BMark.b1, BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist layerList,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist preserved,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist notPreserved,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist refusalLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist gateVerdict,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        layeredRelationGateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        layeredRelationGateEncodeBHist provenance]

def layeredRelationGateFromEventFlow : EventFlow → Option LayeredRelationGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | layerList :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | preserved :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | notPreserved :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refusalLedger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | gateVerdict :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | continuation ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (LayeredRelationGateUp.mk
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            sourceLeft)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            sourceRight)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            layerList)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            preserved)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            notPreserved)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            refusalLedger)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            gateVerdict)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            transport)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            continuation)
                                                                                          (layeredRelationGateDecodeBHist
                                                                                            provenance))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem layeredRelationGate_round_trip :
    ∀ x : LayeredRelationGateUp,
      layeredRelationGateFromEventFlow (layeredRelationGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight layerList preserved notPreserved refusalLedger gateVerdict
      transport continuation provenance =>
      change
        some
          (LayeredRelationGateUp.mk
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist sourceLeft))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist sourceRight))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist layerList))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist preserved))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist notPreserved))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist refusalLedger))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist gateVerdict))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist transport))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist continuation))
            (layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist provenance))) =
          some
            (LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved
              notPreserved refusalLedger gateVerdict transport continuation provenance)
      rw [layeredRelationGateDecode_encode_bhist sourceLeft,
        layeredRelationGateDecode_encode_bhist sourceRight,
        layeredRelationGateDecode_encode_bhist layerList,
        layeredRelationGateDecode_encode_bhist preserved,
        layeredRelationGateDecode_encode_bhist notPreserved,
        layeredRelationGateDecode_encode_bhist refusalLedger,
        layeredRelationGateDecode_encode_bhist gateVerdict,
        layeredRelationGateDecode_encode_bhist transport,
        layeredRelationGateDecode_encode_bhist continuation,
        layeredRelationGateDecode_encode_bhist provenance]

private theorem layeredRelationGateToEventFlow_injective {x y : LayeredRelationGateUp} :
    layeredRelationGateToEventFlow x = layeredRelationGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      layeredRelationGateFromEventFlow (layeredRelationGateToEventFlow x) =
        layeredRelationGateFromEventFlow (layeredRelationGateToEventFlow y) :=
    congrArg layeredRelationGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (layeredRelationGate_round_trip x).symm
      (Eq.trans hread (layeredRelationGate_round_trip y)))

instance layeredRelationGateBHistCarrier : BHistCarrier LayeredRelationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := layeredRelationGateToEventFlow
  fromEventFlow := layeredRelationGateFromEventFlow

instance layeredRelationGateChapterTasteGate : ChapterTasteGate LayeredRelationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change layeredRelationGateFromEventFlow (layeredRelationGateToEventFlow x) = some x
    exact layeredRelationGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (layeredRelationGateToEventFlow_injective heq)

instance layeredRelationGateFieldFaithful : FieldFaithful LayeredRelationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LayeredRelationGateUp.mk sourceLeft sourceRight layerList preserved notPreserved
        refusalLedger gateVerdict transport continuation provenance =>
        [sourceLeft, sourceRight, layerList, preserved, notPreserved, refusalLedger,
          gateVerdict, transport, continuation, provenance]
  field_faithful := by
    intro x y h
    cases x with
    | mk sourceLeft₁ sourceRight₁ layerList₁ preserved₁ notPreserved₁ refusalLedger₁
        gateVerdict₁ transport₁ continuation₁ provenance₁ =>
        cases y with
        | mk sourceLeft₂ sourceRight₂ layerList₂ preserved₂ notPreserved₂ refusalLedger₂
            gateVerdict₂ transport₂ continuation₂ provenance₂ =>
            cases h
            rfl

instance layeredRelationGateNontrivial : Nontrivial LayeredRelationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LayeredRelationGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LayeredRelationGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LayeredRelationGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  layeredRelationGateChapterTasteGate

theorem LayeredRelationGateTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LayeredRelationGateUp) ∧
      Nonempty (FieldFaithful LayeredRelationGateUp) ∧
        Nonempty (Nontrivial LayeredRelationGateUp) ∧
          (∀ h : BHist,
            layeredRelationGateDecodeBHist (layeredRelationGateEncodeBHist h) = h) ∧
            (∀ x : LayeredRelationGateUp,
              layeredRelationGateFromEventFlow (layeredRelationGateToEventFlow x) =
                some x) ∧
              (∀ x y : LayeredRelationGateUp,
                layeredRelationGateToEventFlow x = layeredRelationGateToEventFlow y →
                  x = y) ∧
                layeredRelationGateEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨layeredRelationGateChapterTasteGate⟩
  · constructor
    · exact ⟨layeredRelationGateFieldFaithful⟩
    · constructor
      · exact ⟨layeredRelationGateNontrivial⟩
      · constructor
        · exact layeredRelationGateDecode_encode_bhist
        · constructor
          · exact layeredRelationGate_round_trip
          · constructor
            · intro x y heq
              exact layeredRelationGateToEventFlow_injective heq
            · rfl

end BEDC.Derived.LayeredRelationGateUp
