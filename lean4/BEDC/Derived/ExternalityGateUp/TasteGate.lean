import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalityGateUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalityGateUp : Type where
  | mk :
      (apophaticName gateQuestion visibleUse refusalLedger auditReadback transport continuation
        provenance nameCert : BHist) →
      ExternalityGateUp

def externalityGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalityGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalityGateEncodeBHist h

def externalityGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalityGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalityGateDecodeBHist tail)

private theorem externalityGateDecode_encode_bhist :
    ∀ h : BHist, externalityGateDecodeBHist (externalityGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def externalityGateToEventFlow : ExternalityGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalityGateUp.mk apophaticName gateQuestion visibleUse refusalLedger auditReadback
      transport continuation provenance nameCert =>
      [[BMark.b0],
        externalityGateEncodeBHist apophaticName,
        [BMark.b1, BMark.b0],
        externalityGateEncodeBHist gateQuestion,
        [BMark.b1, BMark.b1, BMark.b0],
        externalityGateEncodeBHist visibleUse,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalityGateEncodeBHist refusalLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalityGateEncodeBHist auditReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalityGateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalityGateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        externalityGateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        externalityGateEncodeBHist nameCert]

def externalityGateFromEventFlow : EventFlow → Option ExternalityGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | apophaticName :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | gateQuestion :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | visibleUse :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusalLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | auditReadback :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ExternalityGateUp.mk
                                                                                  (externalityGateDecodeBHist
                                                                                    apophaticName)
                                                                                  (externalityGateDecodeBHist
                                                                                    gateQuestion)
                                                                                  (externalityGateDecodeBHist
                                                                                    visibleUse)
                                                                                  (externalityGateDecodeBHist
                                                                                    refusalLedger)
                                                                                  (externalityGateDecodeBHist
                                                                                    auditReadback)
                                                                                  (externalityGateDecodeBHist
                                                                                    transport)
                                                                                  (externalityGateDecodeBHist
                                                                                    continuation)
                                                                                  (externalityGateDecodeBHist
                                                                                    provenance)
                                                                                  (externalityGateDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem externalityGate_round_trip :
    ∀ x : ExternalityGateUp,
      externalityGateFromEventFlow (externalityGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk apophaticName gateQuestion visibleUse refusalLedger auditReadback transport
      continuation provenance nameCert =>
      change
        some
            (ExternalityGateUp.mk
              (externalityGateDecodeBHist (externalityGateEncodeBHist apophaticName))
              (externalityGateDecodeBHist (externalityGateEncodeBHist gateQuestion))
              (externalityGateDecodeBHist (externalityGateEncodeBHist visibleUse))
              (externalityGateDecodeBHist (externalityGateEncodeBHist refusalLedger))
              (externalityGateDecodeBHist (externalityGateEncodeBHist auditReadback))
              (externalityGateDecodeBHist (externalityGateEncodeBHist transport))
              (externalityGateDecodeBHist (externalityGateEncodeBHist continuation))
              (externalityGateDecodeBHist (externalityGateEncodeBHist provenance))
              (externalityGateDecodeBHist (externalityGateEncodeBHist nameCert))) =
          some
            (ExternalityGateUp.mk apophaticName gateQuestion visibleUse refusalLedger
              auditReadback transport continuation provenance nameCert)
      rw [externalityGateDecode_encode_bhist apophaticName,
        externalityGateDecode_encode_bhist gateQuestion,
        externalityGateDecode_encode_bhist visibleUse,
        externalityGateDecode_encode_bhist refusalLedger,
        externalityGateDecode_encode_bhist auditReadback,
        externalityGateDecode_encode_bhist transport,
        externalityGateDecode_encode_bhist continuation,
        externalityGateDecode_encode_bhist provenance,
        externalityGateDecode_encode_bhist nameCert]

private theorem externalityGateToEventFlow_injective {x y : ExternalityGateUp} :
    externalityGateToEventFlow x = externalityGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalityGateFromEventFlow (externalityGateToEventFlow x) =
        externalityGateFromEventFlow (externalityGateToEventFlow y) :=
    congrArg externalityGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalityGate_round_trip x).symm
      (Eq.trans hread (externalityGate_round_trip y)))

instance externalityGateBHistCarrier : BHistCarrier ExternalityGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalityGateToEventFlow
  fromEventFlow := externalityGateFromEventFlow

instance externalityGateChapterTasteGate : ChapterTasteGate ExternalityGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change externalityGateFromEventFlow (externalityGateToEventFlow x) = some x
    exact externalityGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalityGateToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ExternalityGateUp := externalityGateChapterTasteGate

theorem ExternalityGateTasteGate_single_carrier_alignment :
    (∀ h : BHist, externalityGateDecodeBHist (externalityGateEncodeBHist h) = h) ∧
      (∀ x : ExternalityGateUp,
        externalityGateFromEventFlow (externalityGateToEventFlow x) = some x) ∧
        (∀ x y : ExternalityGateUp, externalityGateToEventFlow x = externalityGateToEventFlow y →
          x = y) ∧
          externalityGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact externalityGateDecode_encode_bhist h
  · constructor
    · intro x
      exact externalityGate_round_trip x
    · constructor
      · intro x y heq
        exact externalityGateToEventFlow_injective heq
      · rfl

end BEDC.Derived.ExternalityGateUp
