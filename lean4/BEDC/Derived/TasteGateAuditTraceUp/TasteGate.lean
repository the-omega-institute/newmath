import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TasteGateAuditTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TasteGateAuditTraceUp : Type where
  | mk :
      (candidate origin obligations replay provenance gaps transports routes package name :
        BHist) →
      TasteGateAuditTraceUp

private def tasteGateAuditTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tasteGateAuditTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tasteGateAuditTraceEncodeBHist h

private def tasteGateAuditTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tasteGateAuditTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tasteGateAuditTraceDecodeBHist tail)

private theorem tasteGateAuditTraceDecode_encode_bhist :
    ∀ h : BHist, tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem tasteGateAuditTrace_mk_congr
    {candidate candidate' origin origin' obligations obligations' replay replay'
      provenance provenance' gaps gaps' transports transports' routes routes' package package'
      name name' : BHist}
    (hCandidate : candidate' = candidate)
    (hOrigin : origin' = origin)
    (hObligations : obligations' = obligations)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hGaps : gaps' = gaps)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hPackage : package' = package)
    (hName : name' = name) :
    TasteGateAuditTraceUp.mk candidate' origin' obligations' replay' provenance' gaps'
        transports' routes' package' name' =
      TasteGateAuditTraceUp.mk candidate origin obligations replay provenance gaps transports
        routes package name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCandidate
  cases hOrigin
  cases hObligations
  cases hReplay
  cases hProvenance
  cases hGaps
  cases hTransports
  cases hRoutes
  cases hPackage
  cases hName
  rfl

private def tasteGateAuditTraceToEventFlow : TasteGateAuditTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TasteGateAuditTraceUp.mk candidate origin obligations replay provenance gaps transports routes
      package name =>
      [[BMark.b0],
        tasteGateAuditTraceEncodeBHist candidate,
        [BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist origin,
        [BMark.b1, BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist obligations,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist gaps,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tasteGateAuditTraceEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        tasteGateAuditTraceEncodeBHist name]

private def tasteGateAuditTraceFromEventFlow : EventFlow → Option TasteGateAuditTraceUp
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
              | origin :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | obligations :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | gaps :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transports :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | package :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (TasteGateAuditTraceUp.mk
                                                                                          (tasteGateAuditTraceDecodeBHist candidate)
                                                                                          (tasteGateAuditTraceDecodeBHist origin)
                                                                                          (tasteGateAuditTraceDecodeBHist obligations)
                                                                                          (tasteGateAuditTraceDecodeBHist replay)
                                                                                          (tasteGateAuditTraceDecodeBHist provenance)
                                                                                          (tasteGateAuditTraceDecodeBHist gaps)
                                                                                          (tasteGateAuditTraceDecodeBHist transports)
                                                                                          (tasteGateAuditTraceDecodeBHist routes)
                                                                                          (tasteGateAuditTraceDecodeBHist package)
                                                                                          (tasteGateAuditTraceDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem tasteGateAuditTrace_round_trip :
    ∀ x : TasteGateAuditTraceUp,
      tasteGateAuditTraceFromEventFlow (tasteGateAuditTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate origin obligations replay provenance gaps transports routes package name =>
      change
        some
          (TasteGateAuditTraceUp.mk
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist candidate))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist origin))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist obligations))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist replay))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist provenance))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist gaps))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist transports))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist routes))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist package))
            (tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist name))) =
          some
            (TasteGateAuditTraceUp.mk candidate origin obligations replay provenance gaps
              transports routes package name)
      exact
        congrArg some
          (tasteGateAuditTrace_mk_congr
            (tasteGateAuditTraceDecode_encode_bhist candidate)
            (tasteGateAuditTraceDecode_encode_bhist origin)
            (tasteGateAuditTraceDecode_encode_bhist obligations)
            (tasteGateAuditTraceDecode_encode_bhist replay)
            (tasteGateAuditTraceDecode_encode_bhist provenance)
            (tasteGateAuditTraceDecode_encode_bhist gaps)
            (tasteGateAuditTraceDecode_encode_bhist transports)
            (tasteGateAuditTraceDecode_encode_bhist routes)
            (tasteGateAuditTraceDecode_encode_bhist package)
            (tasteGateAuditTraceDecode_encode_bhist name))

private theorem tasteGateAuditTraceToEventFlow_injective {x y : TasteGateAuditTraceUp} :
    tasteGateAuditTraceToEventFlow x = tasteGateAuditTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tasteGateAuditTraceFromEventFlow (tasteGateAuditTraceToEventFlow x) =
        tasteGateAuditTraceFromEventFlow (tasteGateAuditTraceToEventFlow y) :=
    congrArg tasteGateAuditTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tasteGateAuditTrace_round_trip x).symm
      (Eq.trans hread (tasteGateAuditTrace_round_trip y)))

instance tasteGateAuditTraceBHistCarrier : BHistCarrier TasteGateAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tasteGateAuditTraceToEventFlow
  fromEventFlow := tasteGateAuditTraceFromEventFlow

instance tasteGateAuditTraceChapterTasteGate : ChapterTasteGate TasteGateAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tasteGateAuditTraceFromEventFlow (tasteGateAuditTraceToEventFlow x) = some x
    exact tasteGateAuditTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tasteGateAuditTraceToEventFlow_injective heq)

theorem TasteGateAuditTraceUp_single_carrier_alignment :
    (∀ h : BHist, tasteGateAuditTraceDecodeBHist (tasteGateAuditTraceEncodeBHist h) = h) ∧
      tasteGateAuditTraceFromEventFlow
          (tasteGateAuditTraceToEventFlow
            (TasteGateAuditTraceUp.mk BHist.Empty (BHist.e0 BHist.Empty)
              (BHist.e1 BHist.Empty) (BHist.e0 (BHist.e1 BHist.Empty))
              (BHist.e1 (BHist.e0 BHist.Empty)) (BHist.e0 (BHist.e0 BHist.Empty))
              (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e0 (BHist.e0 (BHist.e1 BHist.Empty)))
              (BHist.e1 (BHist.e0 (BHist.e1 BHist.Empty)))
              (BHist.e1 (BHist.e1 (BHist.e0 BHist.Empty))))) =
        some
          (TasteGateAuditTraceUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) (BHist.e0 (BHist.e1 BHist.Empty))
            (BHist.e1 (BHist.e0 BHist.Empty)) (BHist.e0 (BHist.e0 BHist.Empty))
            (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e0 (BHist.e0 (BHist.e1 BHist.Empty)))
            (BHist.e1 (BHist.e0 (BHist.e1 BHist.Empty)))
            (BHist.e1 (BHist.e1 (BHist.e0 BHist.Empty)))) ∧
        tasteGateAuditTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact tasteGateAuditTraceDecode_encode_bhist
  · constructor
    · exact tasteGateAuditTrace_round_trip
        (TasteGateAuditTraceUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) (BHist.e0 (BHist.e1 BHist.Empty))
          (BHist.e1 (BHist.e0 BHist.Empty)) (BHist.e0 (BHist.e0 BHist.Empty))
          (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e0 (BHist.e0 (BHist.e1 BHist.Empty)))
          (BHist.e1 (BHist.e0 (BHist.e1 BHist.Empty)))
          (BHist.e1 (BHist.e1 (BHist.e0 BHist.Empty))))
    · rfl

end BEDC.Derived.TasteGateAuditTraceUp
