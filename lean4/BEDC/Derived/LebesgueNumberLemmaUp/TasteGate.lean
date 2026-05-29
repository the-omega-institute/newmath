import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LebesgueNumberLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LebesgueNumberLemmaUp : Type where
  | mk
      (compact metric cover radiusLedger uniformHandoff transport replay provenance name : BHist) :
      LebesgueNumberLemmaUp
  deriving DecidableEq

def lebesgueNumberLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lebesgueNumberLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lebesgueNumberLemmaEncodeBHist h

def lebesgueNumberLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lebesgueNumberLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lebesgueNumberLemmaDecodeBHist tail)

private theorem lebesgueNumberLemmaDecode_encode_bhist :
    ∀ h : BHist, lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lebesgueNumberLemmaToEventFlow : LebesgueNumberLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LebesgueNumberLemmaUp.mk compact metric cover radiusLedger uniformHandoff transport replay
      provenance name =>
      [[BMark.b0],
        lebesgueNumberLemmaEncodeBHist compact,
        [BMark.b1, BMark.b0],
        lebesgueNumberLemmaEncodeBHist metric,
        [BMark.b1, BMark.b1, BMark.b0],
        lebesgueNumberLemmaEncodeBHist cover,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lebesgueNumberLemmaEncodeBHist radiusLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lebesgueNumberLemmaEncodeBHist uniformHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lebesgueNumberLemmaEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lebesgueNumberLemmaEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        lebesgueNumberLemmaEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        lebesgueNumberLemmaEncodeBHist name]

def lebesgueNumberLemmaFromEventFlow : EventFlow → Option LebesgueNumberLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | compact :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | metric :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cover :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | radiusLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | uniformHandoff :: rest9 =>
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
                                                      | replay :: rest13 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (LebesgueNumberLemmaUp.mk
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    compact)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    metric)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    cover)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    radiusLedger)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    uniformHandoff)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    transport)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    replay)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    provenance)
                                                                                  (lebesgueNumberLemmaDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem lebesgueNumberLemma_round_trip :
    ∀ x : LebesgueNumberLemmaUp,
      lebesgueNumberLemmaFromEventFlow (lebesgueNumberLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compact metric cover radiusLedger uniformHandoff transport replay provenance name =>
      change
        some
          (LebesgueNumberLemmaUp.mk
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist compact))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist metric))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist cover))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist radiusLedger))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist uniformHandoff))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist transport))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist replay))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist provenance))
            (lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist name))) =
          some
            (LebesgueNumberLemmaUp.mk compact metric cover radiusLedger uniformHandoff
              transport replay provenance name)
      rw [lebesgueNumberLemmaDecode_encode_bhist compact,
        lebesgueNumberLemmaDecode_encode_bhist metric,
        lebesgueNumberLemmaDecode_encode_bhist cover,
        lebesgueNumberLemmaDecode_encode_bhist radiusLedger,
        lebesgueNumberLemmaDecode_encode_bhist uniformHandoff,
        lebesgueNumberLemmaDecode_encode_bhist transport,
        lebesgueNumberLemmaDecode_encode_bhist replay,
        lebesgueNumberLemmaDecode_encode_bhist provenance,
        lebesgueNumberLemmaDecode_encode_bhist name]

private theorem lebesgueNumberLemmaToEventFlow_injective {x y : LebesgueNumberLemmaUp} :
    lebesgueNumberLemmaToEventFlow x = lebesgueNumberLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lebesgueNumberLemmaFromEventFlow (lebesgueNumberLemmaToEventFlow x) =
        lebesgueNumberLemmaFromEventFlow (lebesgueNumberLemmaToEventFlow y) :=
    congrArg lebesgueNumberLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lebesgueNumberLemma_round_trip x).symm
      (Eq.trans hread (lebesgueNumberLemma_round_trip y)))

instance lebesgueNumberLemmaBHistCarrier : BHistCarrier LebesgueNumberLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lebesgueNumberLemmaToEventFlow
  fromEventFlow := lebesgueNumberLemmaFromEventFlow

instance lebesgueNumberLemmaChapterTasteGate : ChapterTasteGate LebesgueNumberLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lebesgueNumberLemmaFromEventFlow (lebesgueNumberLemmaToEventFlow x) = some x
    exact lebesgueNumberLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lebesgueNumberLemmaToEventFlow_injective heq)

theorem LebesgueNumberLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, lebesgueNumberLemmaDecodeBHist (lebesgueNumberLemmaEncodeBHist h) = h) ∧
      (∀ x : LebesgueNumberLemmaUp,
        lebesgueNumberLemmaFromEventFlow (lebesgueNumberLemmaToEventFlow x) = some x) ∧
      (∀ x y : LebesgueNumberLemmaUp,
        lebesgueNumberLemmaToEventFlow x = lebesgueNumberLemmaToEventFlow y → x = y) ∧
      lebesgueNumberLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact lebesgueNumberLemmaDecode_encode_bhist
  · constructor
    · exact lebesgueNumberLemma_round_trip
    · constructor
      · intro x y heq
        exact lebesgueNumberLemmaToEventFlow_injective heq
      · rfl

end BEDC.Derived.LebesgueNumberLemmaUp
