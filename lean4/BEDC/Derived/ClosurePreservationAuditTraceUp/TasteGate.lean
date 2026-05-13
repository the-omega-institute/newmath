import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosurePreservationAuditTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosurePreservationAuditTraceUp : Type where
  | mk :
      (shiftRow varSubstRow fullSubstRow betaStepRow betaStarRow transports routes
        provenance name : BHist) →
      ClosurePreservationAuditTraceUp
  deriving DecidableEq

def closurePreservationAuditTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closurePreservationAuditTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closurePreservationAuditTraceEncodeBHist h

def closurePreservationAuditTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closurePreservationAuditTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closurePreservationAuditTraceDecodeBHist tail)

private theorem closurePreservationAuditTraceDecodeEncodeBHist :
    ∀ h : BHist,
      closurePreservationAuditTraceDecodeBHist
        (closurePreservationAuditTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closurePreservationAuditTraceToEventFlow : ClosurePreservationAuditTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosurePreservationAuditTraceUp.mk shiftRow varSubstRow fullSubstRow betaStepRow
      betaStarRow transports routes provenance name =>
      [[BMark.b0],
        closurePreservationAuditTraceEncodeBHist shiftRow,
        [BMark.b1, BMark.b0],
        closurePreservationAuditTraceEncodeBHist varSubstRow,
        [BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditTraceEncodeBHist fullSubstRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditTraceEncodeBHist betaStepRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditTraceEncodeBHist betaStarRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditTraceEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditTraceEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closurePreservationAuditTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closurePreservationAuditTraceEncodeBHist name]

def closurePreservationAuditTraceFromEventFlow :
    EventFlow → Option ClosurePreservationAuditTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | shiftRow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | varSubstRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | fullSubstRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | betaStepRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | betaStarRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | name ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (ClosurePreservationAuditTraceUp.mk
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    shiftRow)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    varSubstRow)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    fullSubstRow)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    betaStepRow)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    betaStarRow)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    transports)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    routes)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    provenance)
                                                                                  (closurePreservationAuditTraceDecodeBHist
                                                                                    name))
                                                                          | _ :: _ =>
                                                                              none

private theorem closurePreservationAuditTraceRoundTrip :
    ∀ x : ClosurePreservationAuditTraceUp,
      closurePreservationAuditTraceFromEventFlow
        (closurePreservationAuditTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk shiftRow varSubstRow fullSubstRow betaStepRow betaStarRow transports routes
      provenance name =>
      change
        some
          (ClosurePreservationAuditTraceUp.mk
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist shiftRow))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist varSubstRow))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist fullSubstRow))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist betaStepRow))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist betaStarRow))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist transports))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist routes))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist provenance))
            (closurePreservationAuditTraceDecodeBHist
              (closurePreservationAuditTraceEncodeBHist name))) =
          some
            (ClosurePreservationAuditTraceUp.mk shiftRow varSubstRow fullSubstRow
              betaStepRow betaStarRow transports routes provenance name)
      rw [closurePreservationAuditTraceDecodeEncodeBHist shiftRow,
        closurePreservationAuditTraceDecodeEncodeBHist varSubstRow,
        closurePreservationAuditTraceDecodeEncodeBHist fullSubstRow,
        closurePreservationAuditTraceDecodeEncodeBHist betaStepRow,
        closurePreservationAuditTraceDecodeEncodeBHist betaStarRow,
        closurePreservationAuditTraceDecodeEncodeBHist transports,
        closurePreservationAuditTraceDecodeEncodeBHist routes,
        closurePreservationAuditTraceDecodeEncodeBHist provenance,
        closurePreservationAuditTraceDecodeEncodeBHist name]

private theorem closurePreservationAuditTraceToEventFlow_injective
    {x y : ClosurePreservationAuditTraceUp} :
    closurePreservationAuditTraceToEventFlow x =
      closurePreservationAuditTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closurePreservationAuditTraceFromEventFlow
          (closurePreservationAuditTraceToEventFlow x) =
        closurePreservationAuditTraceFromEventFlow
          (closurePreservationAuditTraceToEventFlow y) :=
    congrArg closurePreservationAuditTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closurePreservationAuditTraceRoundTrip x).symm
      (Eq.trans hread (closurePreservationAuditTraceRoundTrip y)))

instance closurePreservationAuditTraceBHistCarrier :
    BHistCarrier ClosurePreservationAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closurePreservationAuditTraceToEventFlow
  fromEventFlow := closurePreservationAuditTraceFromEventFlow

instance closurePreservationAuditTraceChapterTasteGate :
    ChapterTasteGate ClosurePreservationAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closurePreservationAuditTraceFromEventFlow
        (closurePreservationAuditTraceToEventFlow x) = some x
    exact closurePreservationAuditTraceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closurePreservationAuditTraceToEventFlow_injective heq)

instance closurePreservationAuditTraceFieldFaithful :
    FieldFaithful ClosurePreservationAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosurePreservationAuditTraceUp.mk shiftRow varSubstRow fullSubstRow betaStepRow
        betaStarRow transports routes provenance name =>
        [shiftRow, varSubstRow, fullSubstRow, betaStepRow, betaStarRow, transports, routes,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk shiftRow₁ varSubstRow₁ fullSubstRow₁ betaStepRow₁ betaStarRow₁ transports₁
        routes₁ provenance₁ name₁ =>
        cases y with
        | mk shiftRow₂ varSubstRow₂ fullSubstRow₂ betaStepRow₂ betaStarRow₂ transports₂
            routes₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

theorem ClosurePreservationAuditTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closurePreservationAuditTraceDecodeBHist
        (closurePreservationAuditTraceEncodeBHist h) = h) ∧
      (∀ x : ClosurePreservationAuditTraceUp,
        closurePreservationAuditTraceFromEventFlow
          (closurePreservationAuditTraceToEventFlow x) = some x) ∧
        (∀ x y : ClosurePreservationAuditTraceUp,
          closurePreservationAuditTraceToEventFlow x =
            closurePreservationAuditTraceToEventFlow y → x = y) ∧
          closurePreservationAuditTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closurePreservationAuditTraceDecodeEncodeBHist
  · constructor
    · exact closurePreservationAuditTraceRoundTrip
    · constructor
      · intro x y heq
        exact closurePreservationAuditTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosurePreservationAuditTraceUp
