import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NontrivialZeroClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NontrivialZeroClassifierUp : Type where
  | mk :
      (zero strip witness trivial realPart comparison transport route provenance name : BHist) →
        NontrivialZeroClassifierUp
  deriving DecidableEq

private def nontrivialZeroClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nontrivialZeroClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nontrivialZeroClassifierEncodeBHist h

private def nontrivialZeroClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nontrivialZeroClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nontrivialZeroClassifierDecodeBHist tail)

private theorem nontrivialZeroClassifierDecodeEncodeBHist :
    ∀ h : BHist,
      nontrivialZeroClassifierDecodeBHist (nontrivialZeroClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def nontrivialZeroClassifierToEventFlow : NontrivialZeroClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NontrivialZeroClassifierUp.mk zero strip witness trivial realPart comparison transport route
      provenance name =>
      [[BMark.b0],
        nontrivialZeroClassifierEncodeBHist zero,
        [BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist strip,
        [BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist trivial,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist realPart,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist comparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        nontrivialZeroClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist name]

private def nontrivialZeroClassifierFromEventFlow :
    EventFlow → Option NontrivialZeroClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | zero :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | strip :: rest3 =>
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
                              | trivial :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realPart :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | comparison :: rest11 =>
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
                                                                                        (NontrivialZeroClassifierUp.mk
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            zero)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            strip)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            witness)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            trivial)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            realPart)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            comparison)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            transport)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            route)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            provenance)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem nontrivialZeroClassifierRoundTrip :
    ∀ x : NontrivialZeroClassifierUp,
      nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk zero strip witness trivial realPart comparison transport route provenance name =>
      change
        some
          (NontrivialZeroClassifierUp.mk
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist zero))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist strip))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist witness))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist trivial))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist realPart))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist comparison))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist transport))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist route))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist provenance))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist name))) =
          some
            (NontrivialZeroClassifierUp.mk zero strip witness trivial realPart comparison
              transport route provenance name)
      rw [nontrivialZeroClassifierDecodeEncodeBHist zero,
        nontrivialZeroClassifierDecodeEncodeBHist strip,
        nontrivialZeroClassifierDecodeEncodeBHist witness,
        nontrivialZeroClassifierDecodeEncodeBHist trivial,
        nontrivialZeroClassifierDecodeEncodeBHist realPart,
        nontrivialZeroClassifierDecodeEncodeBHist comparison,
        nontrivialZeroClassifierDecodeEncodeBHist transport,
        nontrivialZeroClassifierDecodeEncodeBHist route,
        nontrivialZeroClassifierDecodeEncodeBHist provenance,
        nontrivialZeroClassifierDecodeEncodeBHist name]

private theorem nontrivialZeroClassifierToEventFlow_injective
    {x y : NontrivialZeroClassifierUp} :
    nontrivialZeroClassifierToEventFlow x = nontrivialZeroClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow x) =
        nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow y) :=
    congrArg nontrivialZeroClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nontrivialZeroClassifierRoundTrip x).symm
      (Eq.trans hread (nontrivialZeroClassifierRoundTrip y)))

instance nontrivialZeroClassifierBHistCarrier : BHistCarrier NontrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nontrivialZeroClassifierToEventFlow
  fromEventFlow := nontrivialZeroClassifierFromEventFlow

instance nontrivialZeroClassifierChapterTasteGate :
    ChapterTasteGate NontrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow x) = some x
    exact nontrivialZeroClassifierRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nontrivialZeroClassifierToEventFlow_injective heq)

theorem NontrivialZeroClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist, nontrivialZeroClassifierDecodeBHist
        (nontrivialZeroClassifierEncodeBHist h) = h) ∧
      (∀ x : NontrivialZeroClassifierUp,
        nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow x) =
          some x) ∧
        (∀ x y : NontrivialZeroClassifierUp,
          nontrivialZeroClassifierToEventFlow x = nontrivialZeroClassifierToEventFlow y →
            x = y) ∧
          nontrivialZeroClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact nontrivialZeroClassifierDecodeEncodeBHist
  · constructor
    · intro x
      exact nontrivialZeroClassifierRoundTrip x
    · constructor
      · intro x y heq
        exact nontrivialZeroClassifierToEventFlow_injective heq
      · rfl

end BEDC.Derived.NontrivialZeroClassifierUp
