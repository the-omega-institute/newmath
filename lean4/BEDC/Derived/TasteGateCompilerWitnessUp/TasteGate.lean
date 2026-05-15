import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TasteGateCompilerWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TasteGateCompilerWitnessUp : Type where
  | mk :
      (candidate tasteGate eventFlow noHidden roundTrip layerSeparation dependencyLedger
        auditResult transports routes provenance name : BHist) →
        TasteGateCompilerWitnessUp
  deriving DecidableEq

private def tasteGateCompilerWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tasteGateCompilerWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tasteGateCompilerWitnessEncodeBHist h

private def tasteGateCompilerWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tasteGateCompilerWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tasteGateCompilerWitnessDecodeBHist tail)

private theorem tasteGateCompilerWitnessDecodeEncodeBHist :
    ∀ h : BHist,
      tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def tasteGateCompilerWitnessToEventFlow : TasteGateCompilerWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TasteGateCompilerWitnessUp.mk candidate tasteGate eventFlow noHidden roundTrip
      layerSeparation dependencyLedger auditResult transports routes provenance name =>
      [[BMark.b0],
        tasteGateCompilerWitnessEncodeBHist candidate,
        [BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist tasteGate,
        [BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist eventFlow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist noHidden,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist roundTrip,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist layerSeparation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist dependencyLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tasteGateCompilerWitnessEncodeBHist auditResult,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateCompilerWitnessEncodeBHist name]

private def tasteGateCompilerWitnessFromEventFlow :
    EventFlow → Option TasteGateCompilerWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | candidate :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | tasteGate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | eventFlow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | noHidden :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | roundTrip :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | layerSeparation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | dependencyLedger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | auditResult :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transports ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | routes ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] => none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | name ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (TasteGateCompilerWitnessUp.mk
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            candidate)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            tasteGate)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            eventFlow)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            noHidden)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            roundTrip)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            layerSeparation)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            dependencyLedger)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            auditResult)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            transports)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            routes)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            provenance)
                                                                                                          (tasteGateCompilerWitnessDecodeBHist
                                                                                                            name))
                                                                                                  | _ ::
                                                                                                      _ =>
                                                                                                      none

private theorem tasteGateCompilerWitnessRoundTrip :
    ∀ x : TasteGateCompilerWitnessUp,
      tasteGateCompilerWitnessFromEventFlow (tasteGateCompilerWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate tasteGate eventFlow noHidden roundTrip layerSeparation dependencyLedger
      auditResult transports routes provenance name =>
      change
        some
          (TasteGateCompilerWitnessUp.mk
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist candidate))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist tasteGate))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist eventFlow))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist noHidden))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist roundTrip))
            (tasteGateCompilerWitnessDecodeBHist
              (tasteGateCompilerWitnessEncodeBHist layerSeparation))
            (tasteGateCompilerWitnessDecodeBHist
              (tasteGateCompilerWitnessEncodeBHist dependencyLedger))
            (tasteGateCompilerWitnessDecodeBHist
              (tasteGateCompilerWitnessEncodeBHist auditResult))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist transports))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist routes))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist provenance))
            (tasteGateCompilerWitnessDecodeBHist (tasteGateCompilerWitnessEncodeBHist name))) =
          some
            (TasteGateCompilerWitnessUp.mk candidate tasteGate eventFlow noHidden roundTrip
              layerSeparation dependencyLedger auditResult transports routes provenance name)
      rw [tasteGateCompilerWitnessDecodeEncodeBHist candidate,
        tasteGateCompilerWitnessDecodeEncodeBHist tasteGate,
        tasteGateCompilerWitnessDecodeEncodeBHist eventFlow,
        tasteGateCompilerWitnessDecodeEncodeBHist noHidden,
        tasteGateCompilerWitnessDecodeEncodeBHist roundTrip,
        tasteGateCompilerWitnessDecodeEncodeBHist layerSeparation,
        tasteGateCompilerWitnessDecodeEncodeBHist dependencyLedger,
        tasteGateCompilerWitnessDecodeEncodeBHist auditResult,
        tasteGateCompilerWitnessDecodeEncodeBHist transports,
        tasteGateCompilerWitnessDecodeEncodeBHist routes,
        tasteGateCompilerWitnessDecodeEncodeBHist provenance,
        tasteGateCompilerWitnessDecodeEncodeBHist name]

private theorem tasteGateCompilerWitnessToEventFlow_injective
    {x y : TasteGateCompilerWitnessUp} :
    tasteGateCompilerWitnessToEventFlow x = tasteGateCompilerWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tasteGateCompilerWitnessFromEventFlow (tasteGateCompilerWitnessToEventFlow x) =
        tasteGateCompilerWitnessFromEventFlow (tasteGateCompilerWitnessToEventFlow y) :=
    congrArg tasteGateCompilerWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tasteGateCompilerWitnessRoundTrip x).symm
      (Eq.trans hread (tasteGateCompilerWitnessRoundTrip y)))

instance tasteGateCompilerWitnessBHistCarrier : BHistCarrier TasteGateCompilerWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tasteGateCompilerWitnessToEventFlow
  fromEventFlow := tasteGateCompilerWitnessFromEventFlow

instance tasteGateCompilerWitnessChapterTasteGate :
    ChapterTasteGate TasteGateCompilerWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      tasteGateCompilerWitnessFromEventFlow (tasteGateCompilerWitnessToEventFlow x) = some x
    exact tasteGateCompilerWitnessRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tasteGateCompilerWitnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TasteGateCompilerWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tasteGateCompilerWitnessChapterTasteGate

theorem TasteGateCompilerWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, tasteGateCompilerWitnessDecodeBHist
        (tasteGateCompilerWitnessEncodeBHist h) = h) ∧
      (∀ x : TasteGateCompilerWitnessUp,
        tasteGateCompilerWitnessFromEventFlow (tasteGateCompilerWitnessToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGateCompilerWitnessUp,
          tasteGateCompilerWitnessToEventFlow x = tasteGateCompilerWitnessToEventFlow y →
            x = y) ∧
          tasteGateCompilerWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact tasteGateCompilerWitnessDecodeEncodeBHist
  · constructor
    · intro x
      exact tasteGateCompilerWitnessRoundTrip x
    · constructor
      · intro x y heq
        exact tasteGateCompilerWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.TasteGateCompilerWitnessUp
