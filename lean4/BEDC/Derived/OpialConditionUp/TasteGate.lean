import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OpialConditionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OpialConditionUp : Type where
  | mk
      (metric banach sequence window limit comparison handoff readback transport replay
        provenance name : BHist) :
      OpialConditionUp
  deriving DecidableEq

def opialConditionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: opialConditionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: opialConditionEncodeBHist h

def opialConditionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (opialConditionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (opialConditionDecodeBHist tail)

private theorem OpialConditionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, opialConditionDecodeBHist (opialConditionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def opialConditionFields : OpialConditionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OpialConditionUp.mk metric banach sequence window limit comparison handoff readback
      transport replay provenance name =>
      [metric, banach, sequence, window, limit, comparison, handoff, readback, transport,
        replay, provenance, name]

def opialConditionToEventFlow : OpialConditionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (opialConditionFields x).map opialConditionEncodeBHist

def opialConditionFromEventFlow : EventFlow -> Option OpialConditionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | metric :: rest0 =>
      match rest0 with
      | [] => none
      | banach :: rest1 =>
          match rest1 with
          | [] => none
          | sequence :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | limit :: rest4 =>
                      match rest4 with
                      | [] => none
                      | comparison :: rest5 =>
                          match rest5 with
                          | [] => none
                          | handoff :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (OpialConditionUp.mk
                                                          (opialConditionDecodeBHist metric)
                                                          (opialConditionDecodeBHist banach)
                                                          (opialConditionDecodeBHist sequence)
                                                          (opialConditionDecodeBHist window)
                                                          (opialConditionDecodeBHist limit)
                                                          (opialConditionDecodeBHist comparison)
                                                          (opialConditionDecodeBHist handoff)
                                                          (opialConditionDecodeBHist readback)
                                                          (opialConditionDecodeBHist transport)
                                                          (opialConditionDecodeBHist replay)
                                                          (opialConditionDecodeBHist provenance)
                                                          (opialConditionDecodeBHist name))
                                                  | _ :: _ => none

private theorem OpialConditionTasteGate_single_carrier_alignment_round_trip :
    forall x : OpialConditionUp,
      opialConditionFromEventFlow (opialConditionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric banach sequence window limit comparison handoff readback transport replay
      provenance name =>
      change
        some
            (OpialConditionUp.mk
              (opialConditionDecodeBHist (opialConditionEncodeBHist metric))
              (opialConditionDecodeBHist (opialConditionEncodeBHist banach))
              (opialConditionDecodeBHist (opialConditionEncodeBHist sequence))
              (opialConditionDecodeBHist (opialConditionEncodeBHist window))
              (opialConditionDecodeBHist (opialConditionEncodeBHist limit))
              (opialConditionDecodeBHist (opialConditionEncodeBHist comparison))
              (opialConditionDecodeBHist (opialConditionEncodeBHist handoff))
              (opialConditionDecodeBHist (opialConditionEncodeBHist readback))
              (opialConditionDecodeBHist (opialConditionEncodeBHist transport))
              (opialConditionDecodeBHist (opialConditionEncodeBHist replay))
              (opialConditionDecodeBHist (opialConditionEncodeBHist provenance))
              (opialConditionDecodeBHist (opialConditionEncodeBHist name))) =
          some
            (OpialConditionUp.mk metric banach sequence window limit comparison handoff
              readback transport replay provenance name)
      rw [OpialConditionTasteGate_single_carrier_alignment_decode_encode metric,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode banach,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode sequence,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode window,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode limit,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode comparison,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode handoff,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode readback,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode transport,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode replay,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode provenance,
        OpialConditionTasteGate_single_carrier_alignment_decode_encode name]

private theorem OpialConditionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OpialConditionUp} :
    opialConditionToEventFlow x = opialConditionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      opialConditionFromEventFlow (opialConditionToEventFlow x) =
        opialConditionFromEventFlow (opialConditionToEventFlow y) :=
    congrArg opialConditionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OpialConditionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OpialConditionTasteGate_single_carrier_alignment_round_trip y)))

private theorem OpialConditionTasteGate_single_carrier_alignment_field_faithful :
    forall x y : OpialConditionUp, opialConditionFields x = opialConditionFields y -> x = y :=
  by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk metric₁ banach₁ sequence₁ window₁ limit₁ comparison₁ handoff₁ readback₁
        transport₁ replay₁ provenance₁ name₁ =>
        cases y with
        | mk metric₂ banach₂ sequence₂ window₂ limit₂ comparison₂ handoff₂ readback₂
            transport₂ replay₂ provenance₂ name₂ =>
            cases hfields
            rfl

instance opialConditionBHistCarrier : BHistCarrier OpialConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := opialConditionToEventFlow
  fromEventFlow := opialConditionFromEventFlow

instance opialConditionChapterTasteGate : ChapterTasteGate OpialConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (OpialConditionTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (OpialConditionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance opialConditionFieldFaithful : FieldFaithful OpialConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := opialConditionFields
  field_faithful := OpialConditionTasteGate_single_carrier_alignment_field_faithful

instance opialConditionNontrivial : BEDC.Meta.TasteGate.Nontrivial OpialConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OpialConditionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OpialConditionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OpialConditionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  opialConditionChapterTasteGate

theorem OpialConditionTasteGate_single_carrier_alignment :
    (forall h : BHist, opialConditionDecodeBHist (opialConditionEncodeBHist h) = h) ∧
      (forall x : OpialConditionUp,
        opialConditionFromEventFlow (opialConditionToEventFlow x) = some x) ∧
        (forall x y : OpialConditionUp,
          opialConditionToEventFlow x = opialConditionToEventFlow y -> x = y) ∧
          opialConditionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact OpialConditionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact OpialConditionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact OpialConditionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.OpialConditionUp
