import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SelfReferenceTruthBranchUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SelfReferenceTruthBranchUp : Type where
  | mk :
      (selfDescription diagonalRequest certificateQuery forbiddenBranch socketReport transport
        continuation provenance nameCert : BHist) →
      SelfReferenceTruthBranchUp
  deriving DecidableEq

def selfReferenceTruthBranchEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: selfReferenceTruthBranchEncodeBHist h
  | BHist.e1 h => BMark.b1 :: selfReferenceTruthBranchEncodeBHist h

def selfReferenceTruthBranchDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (selfReferenceTruthBranchDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (selfReferenceTruthBranchDecodeBHist tail)

private theorem selfReferenceTruthBranchDecodeEncodeBHist :
    ∀ h : BHist,
      selfReferenceTruthBranchDecodeBHist (selfReferenceTruthBranchEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def selfReferenceTruthBranchToEventFlow : SelfReferenceTruthBranchUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SelfReferenceTruthBranchUp.mk selfDescription diagonalRequest certificateQuery
      forbiddenBranch socketReport transport continuation provenance nameCert =>
      [[BMark.b0],
        selfReferenceTruthBranchEncodeBHist selfDescription,
        [BMark.b1, BMark.b0],
        selfReferenceTruthBranchEncodeBHist diagonalRequest,
        [BMark.b1, BMark.b1, BMark.b0],
        selfReferenceTruthBranchEncodeBHist certificateQuery,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfReferenceTruthBranchEncodeBHist forbiddenBranch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfReferenceTruthBranchEncodeBHist socketReport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfReferenceTruthBranchEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfReferenceTruthBranchEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        selfReferenceTruthBranchEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        selfReferenceTruthBranchEncodeBHist nameCert]

private def selfReferenceTruthBranchDecodePacket
    (selfDescription diagonalRequest certificateQuery forbiddenBranch socketReport transport
      continuation provenance nameCert : RawEvent) : SelfReferenceTruthBranchUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SelfReferenceTruthBranchUp.mk
    (selfReferenceTruthBranchDecodeBHist selfDescription)
    (selfReferenceTruthBranchDecodeBHist diagonalRequest)
    (selfReferenceTruthBranchDecodeBHist certificateQuery)
    (selfReferenceTruthBranchDecodeBHist forbiddenBranch)
    (selfReferenceTruthBranchDecodeBHist socketReport)
    (selfReferenceTruthBranchDecodeBHist transport)
    (selfReferenceTruthBranchDecodeBHist continuation)
    (selfReferenceTruthBranchDecodeBHist provenance)
    (selfReferenceTruthBranchDecodeBHist nameCert)

def selfReferenceTruthBranchFromEventFlow : EventFlow → Option SelfReferenceTruthBranchUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selfDescription :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | diagonalRequest :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | certificateQuery :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | forbiddenBranch :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | socketReport :: rest9 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (selfReferenceTruthBranchDecodePacket
                                                                                  selfDescription
                                                                                  diagonalRequest
                                                                                  certificateQuery
                                                                                  forbiddenBranch
                                                                                  socketReport
                                                                                  transport
                                                                                  continuation
                                                                                  provenance
                                                                                  nameCert)
                                                                          | _ :: _ => none

private theorem selfReferenceTruthBranchMkCongr
    {selfDescription selfDescription' diagonalRequest diagonalRequest' certificateQuery
      certificateQuery' forbiddenBranch forbiddenBranch' socketReport socketReport'
      transport transport' continuation continuation' provenance provenance' nameCert
      nameCert' : BHist}
    (hSelfDescription : selfDescription' = selfDescription)
    (hDiagonalRequest : diagonalRequest' = diagonalRequest)
    (hCertificateQuery : certificateQuery' = certificateQuery)
    (hForbiddenBranch : forbiddenBranch' = forbiddenBranch)
    (hSocketReport : socketReport' = socketReport)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    SelfReferenceTruthBranchUp.mk selfDescription' diagonalRequest' certificateQuery'
        forbiddenBranch' socketReport' transport' continuation' provenance' nameCert' =
      SelfReferenceTruthBranchUp.mk selfDescription diagonalRequest certificateQuery
        forbiddenBranch socketReport transport continuation provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSelfDescription
  cases hDiagonalRequest
  cases hCertificateQuery
  cases hForbiddenBranch
  cases hSocketReport
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

private theorem selfReferenceTruthBranchRoundTrip :
    ∀ x : SelfReferenceTruthBranchUp,
      selfReferenceTruthBranchFromEventFlow (selfReferenceTruthBranchToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk selfDescription diagonalRequest certificateQuery forbiddenBranch socketReport transport
      continuation provenance nameCert =>
      change
        some
          (selfReferenceTruthBranchDecodePacket
            (selfReferenceTruthBranchEncodeBHist selfDescription)
            (selfReferenceTruthBranchEncodeBHist diagonalRequest)
            (selfReferenceTruthBranchEncodeBHist certificateQuery)
            (selfReferenceTruthBranchEncodeBHist forbiddenBranch)
            (selfReferenceTruthBranchEncodeBHist socketReport)
            (selfReferenceTruthBranchEncodeBHist transport)
            (selfReferenceTruthBranchEncodeBHist continuation)
            (selfReferenceTruthBranchEncodeBHist provenance)
            (selfReferenceTruthBranchEncodeBHist nameCert)) =
          some
            (SelfReferenceTruthBranchUp.mk selfDescription diagonalRequest certificateQuery
              forbiddenBranch socketReport transport continuation provenance nameCert)
      unfold selfReferenceTruthBranchDecodePacket
      exact
        congrArg some
          (selfReferenceTruthBranchMkCongr
            (selfReferenceTruthBranchDecodeEncodeBHist selfDescription)
            (selfReferenceTruthBranchDecodeEncodeBHist diagonalRequest)
            (selfReferenceTruthBranchDecodeEncodeBHist certificateQuery)
            (selfReferenceTruthBranchDecodeEncodeBHist forbiddenBranch)
            (selfReferenceTruthBranchDecodeEncodeBHist socketReport)
            (selfReferenceTruthBranchDecodeEncodeBHist transport)
            (selfReferenceTruthBranchDecodeEncodeBHist continuation)
            (selfReferenceTruthBranchDecodeEncodeBHist provenance)
            (selfReferenceTruthBranchDecodeEncodeBHist nameCert))

private theorem selfReferenceTruthBranchToEventFlow_injective
    {x y : SelfReferenceTruthBranchUp} :
    selfReferenceTruthBranchToEventFlow x = selfReferenceTruthBranchToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      selfReferenceTruthBranchFromEventFlow (selfReferenceTruthBranchToEventFlow x) =
        selfReferenceTruthBranchFromEventFlow (selfReferenceTruthBranchToEventFlow y) :=
    congrArg selfReferenceTruthBranchFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (selfReferenceTruthBranchRoundTrip x).symm
      (Eq.trans hread (selfReferenceTruthBranchRoundTrip y)))

instance selfReferenceTruthBranchBHistCarrier : BHistCarrier SelfReferenceTruthBranchUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := selfReferenceTruthBranchToEventFlow
  fromEventFlow := selfReferenceTruthBranchFromEventFlow

instance selfReferenceTruthBranchChapterTasteGate :
    ChapterTasteGate SelfReferenceTruthBranchUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change selfReferenceTruthBranchFromEventFlow (selfReferenceTruthBranchToEventFlow x) =
      some x
    exact selfReferenceTruthBranchRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (selfReferenceTruthBranchToEventFlow_injective heq)

theorem SelfReferenceTruthBranchTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        selfReferenceTruthBranchDecodeBHist (selfReferenceTruthBranchEncodeBHist h) = h) ∧
      (∀ x : SelfReferenceTruthBranchUp,
        selfReferenceTruthBranchFromEventFlow (selfReferenceTruthBranchToEventFlow x) =
          some x) ∧
        (∀ x y : SelfReferenceTruthBranchUp,
          selfReferenceTruthBranchToEventFlow x = selfReferenceTruthBranchToEventFlow y →
            x = y) ∧
          selfReferenceTruthBranchEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact And.intro selfReferenceTruthBranchDecodeEncodeBHist
    (And.intro selfReferenceTruthBranchRoundTrip
      (And.intro
        (by
          intro x y heq
          exact selfReferenceTruthBranchToEventFlow_injective heq)
        rfl))

end BEDC.Derived.SelfReferenceTruthBranchUp
