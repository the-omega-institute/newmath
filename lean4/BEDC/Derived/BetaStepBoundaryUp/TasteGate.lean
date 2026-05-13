import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BetaStepBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BetaStepBoundaryUp : Type where
  | mk :
      (rule conversion obstruction transport route provenance name : BHist) →
      BetaStepBoundaryUp
  deriving DecidableEq

private def betaStepBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: betaStepBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: betaStepBoundaryEncodeBHist h

private def betaStepBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (betaStepBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (betaStepBoundaryDecodeBHist tail)

private theorem betaStepBoundary_decode_encode_bhist :
    ∀ h : BHist,
      betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def betaStepBoundaryToEventFlow : BetaStepBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BetaStepBoundaryUp.mk rule conversion obstruction transport route provenance name =>
      [[BMark.b0],
        betaStepBoundaryEncodeBHist rule,
        [BMark.b1, BMark.b0],
        betaStepBoundaryEncodeBHist conversion,
        [BMark.b1, BMark.b1, BMark.b0],
        betaStepBoundaryEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaStepBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaStepBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaStepBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaStepBoundaryEncodeBHist name]

private def betaStepBoundaryFromEventFlow : EventFlow → Option BetaStepBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | rule :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | conversion :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | obstruction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (BetaStepBoundaryUp.mk
                                                                  (betaStepBoundaryDecodeBHist
                                                                    rule)
                                                                  (betaStepBoundaryDecodeBHist
                                                                    conversion)
                                                                  (betaStepBoundaryDecodeBHist
                                                                    obstruction)
                                                                  (betaStepBoundaryDecodeBHist
                                                                    transport)
                                                                  (betaStepBoundaryDecodeBHist
                                                                    route)
                                                                  (betaStepBoundaryDecodeBHist
                                                                    provenance)
                                                                  (betaStepBoundaryDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem betaStepBoundary_round_trip :
    ∀ x : BetaStepBoundaryUp,
      betaStepBoundaryFromEventFlow (betaStepBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rule conversion obstruction transport route provenance name =>
      change
        some
          (BetaStepBoundaryUp.mk
            (betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist rule))
            (betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist conversion))
            (betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist obstruction))
            (betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist transport))
            (betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist route))
            (betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist provenance))
            (betaStepBoundaryDecodeBHist (betaStepBoundaryEncodeBHist name))) =
          some
            (BetaStepBoundaryUp.mk rule conversion obstruction transport route provenance name)
      rw [betaStepBoundary_decode_encode_bhist rule,
        betaStepBoundary_decode_encode_bhist conversion,
        betaStepBoundary_decode_encode_bhist obstruction,
        betaStepBoundary_decode_encode_bhist transport,
        betaStepBoundary_decode_encode_bhist route,
        betaStepBoundary_decode_encode_bhist provenance,
        betaStepBoundary_decode_encode_bhist name]

private theorem betaStepBoundaryToEventFlow_injective {x y : BetaStepBoundaryUp} :
    betaStepBoundaryToEventFlow x = betaStepBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      betaStepBoundaryFromEventFlow (betaStepBoundaryToEventFlow x) =
        betaStepBoundaryFromEventFlow (betaStepBoundaryToEventFlow y) :=
    congrArg betaStepBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (betaStepBoundary_round_trip x).symm
      (Eq.trans hread (betaStepBoundary_round_trip y)))

instance betaStepBoundaryBHistCarrier : BHistCarrier BetaStepBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := betaStepBoundaryToEventFlow
  fromEventFlow := betaStepBoundaryFromEventFlow

instance betaStepBoundaryChapterTasteGate : ChapterTasteGate BetaStepBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change betaStepBoundaryFromEventFlow (betaStepBoundaryToEventFlow x) = some x
    exact betaStepBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (betaStepBoundaryToEventFlow_injective heq)

instance betaStepBoundaryFieldFaithful : FieldFaithful BetaStepBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BetaStepBoundaryUp.mk rule conversion obstruction transport route provenance name =>
        [rule, conversion, obstruction, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk rule₁ conversion₁ obstruction₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk rule₂ conversion₂ obstruction₂ transport₂ route₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

def taste_gate : ChapterTasteGate BetaStepBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  betaStepBoundaryChapterTasteGate

theorem BetaStepBoundaryTasteGate_single_carrier_alignment :
    ChapterTasteGate BetaStepBoundaryUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact taste_gate

end BEDC.Derived.BetaStepBoundaryUp
