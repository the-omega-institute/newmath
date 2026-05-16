import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompressionDescentAuditUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompressionDescentAuditUp : Type where
  | mk :
      (tower endpoint operation descent ledger failure transport provenance name : BHist) →
        CompressionDescentAuditUp
  deriving DecidableEq

def compressionDescentAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compressionDescentAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compressionDescentAuditEncodeBHist h

def compressionDescentAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compressionDescentAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compressionDescentAuditDecodeBHist tail)

private theorem compressionDescentAuditDecode_encode_bhist :
    ∀ h : BHist,
      compressionDescentAuditDecodeBHist (compressionDescentAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compressionDescentAuditFields : CompressionDescentAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure transport
      provenance name =>
      [tower, endpoint, operation, descent, ledger, failure, transport, provenance, name]

private theorem compressionDescentAudit_mk_congr
    {tower tower' endpoint endpoint' operation operation' descent descent' ledger ledger'
      failure failure' transport transport' provenance provenance' name name' : BHist}
    (hTower : tower' = tower)
    (hEndpoint : endpoint' = endpoint)
    (hOperation : operation' = operation)
    (hDescent : descent' = descent)
    (hLedger : ledger' = ledger)
    (hFailure : failure' = failure)
    (hTransport : transport' = transport)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CompressionDescentAuditUp.mk tower' endpoint' operation' descent' ledger' failure'
        transport' provenance' name' =
      CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure transport
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTower
  cases hEndpoint
  cases hOperation
  cases hDescent
  cases hLedger
  cases hFailure
  cases hTransport
  cases hProvenance
  cases hName
  rfl

def compressionDescentAuditToEventFlow :
    CompressionDescentAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure transport
      provenance name =>
      [[BMark.b0],
        compressionDescentAuditEncodeBHist tower,
        [BMark.b1, BMark.b0],
        compressionDescentAuditEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b0],
        compressionDescentAuditEncodeBHist operation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionDescentAuditEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionDescentAuditEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionDescentAuditEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionDescentAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compressionDescentAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compressionDescentAuditEncodeBHist name]

def compressionDescentAuditFromEventFlow :
    EventFlow → Option CompressionDescentAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | tower :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | endpoint :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | operation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | descent :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | ledger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | failure :: rest11 =>
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
                                                                                (CompressionDescentAuditUp.mk
                                                                                  (compressionDescentAuditDecodeBHist tower)
                                                                                  (compressionDescentAuditDecodeBHist endpoint)
                                                                                  (compressionDescentAuditDecodeBHist operation)
                                                                                  (compressionDescentAuditDecodeBHist descent)
                                                                                  (compressionDescentAuditDecodeBHist ledger)
                                                                                  (compressionDescentAuditDecodeBHist failure)
                                                                                  (compressionDescentAuditDecodeBHist transport)
                                                                                  (compressionDescentAuditDecodeBHist provenance)
                                                                                  (compressionDescentAuditDecodeBHist name))
                                                                          | _ :: _ => none

private theorem compressionDescentAudit_round_trip :
    ∀ x : CompressionDescentAuditUp,
      compressionDescentAuditFromEventFlow
        (compressionDescentAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tower endpoint operation descent ledger failure transport provenance name =>
      change
        some
          (CompressionDescentAuditUp.mk
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist tower))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist endpoint))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist operation))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist descent))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist ledger))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist failure))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist transport))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist provenance))
            (compressionDescentAuditDecodeBHist
              (compressionDescentAuditEncodeBHist name))) =
          some
            (CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure
              transport provenance name)
      exact
        congrArg some
          (compressionDescentAudit_mk_congr
            (compressionDescentAuditDecode_encode_bhist tower)
            (compressionDescentAuditDecode_encode_bhist endpoint)
            (compressionDescentAuditDecode_encode_bhist operation)
            (compressionDescentAuditDecode_encode_bhist descent)
            (compressionDescentAuditDecode_encode_bhist ledger)
            (compressionDescentAuditDecode_encode_bhist failure)
            (compressionDescentAuditDecode_encode_bhist transport)
            (compressionDescentAuditDecode_encode_bhist provenance)
            (compressionDescentAuditDecode_encode_bhist name))

private theorem compressionDescentAuditToEventFlow_injective
    {x y : CompressionDescentAuditUp} :
    compressionDescentAuditToEventFlow x =
      compressionDescentAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : some x = some y := by
    calc
      some x =
          compressionDescentAuditFromEventFlow (compressionDescentAuditToEventFlow x) :=
            (compressionDescentAudit_round_trip x).symm
      _ = compressionDescentAuditFromEventFlow (compressionDescentAuditToEventFlow y) :=
            congrArg compressionDescentAuditFromEventFlow heq
      _ = some y := compressionDescentAudit_round_trip y
  exact Option.some.inj hread

instance compressionDescentAuditBHistCarrier :
    BHistCarrier CompressionDescentAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compressionDescentAuditToEventFlow
  fromEventFlow := compressionDescentAuditFromEventFlow

instance taste_gate :
    ChapterTasteGate CompressionDescentAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := compressionDescentAudit_round_trip
  layer_separation := by
    intro x y hneq hflow
    exact hneq (compressionDescentAuditToEventFlow_injective hflow)

instance compressionDescentAuditFieldFaithful :
    FieldFaithful CompressionDescentAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compressionDescentAuditFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk tower₁ endpoint₁ operation₁ descent₁ ledger₁ failure₁ transport₁ provenance₁ name₁ =>
        cases y with
        | mk tower₂ endpoint₂ operation₂ descent₂ ledger₂ failure₂ transport₂ provenance₂ name₂ =>
            injection h with hTower t1
            injection t1 with hEndpoint t2
            injection t2 with hOperation t3
            injection t3 with hDescent t4
            injection t4 with hLedger t5
            injection t5 with hFailure t6
            injection t6 with hTransport t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            cases hTower
            cases hEndpoint
            cases hOperation
            cases hDescent
            cases hLedger
            cases hFailure
            cases hTransport
            cases hProvenance
            cases hName
            rfl

instance compressionDescentAuditNontrivial :
    Nontrivial CompressionDescentAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompressionDescentAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompressionDescentAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompressionDescentAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compressionDescentAuditDecodeBHist (compressionDescentAuditEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate CompressionDescentAuditUp) ∧
        Nonempty (FieldFaithful CompressionDescentAuditUp) ∧
          Nonempty (Nontrivial CompressionDescentAuditUp) ∧
            compressionDescentAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact compressionDescentAuditDecode_encode_bhist
  · constructor
    · exact ⟨taste_gate⟩
    · constructor
      · exact ⟨compressionDescentAuditFieldFaithful⟩
      · constructor
        · exact ⟨compressionDescentAuditNontrivial⟩
        · rfl

end BEDC.Derived.CompressionDescentAuditUp.TasteGate
