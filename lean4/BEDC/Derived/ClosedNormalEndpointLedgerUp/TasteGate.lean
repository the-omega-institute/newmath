import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalEndpointLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalEndpointLedgerUp : Type where
  | mk :
      (typed closed beta falseRow route transport continuation provenance nameCert : BHist) →
      ClosedNormalEndpointLedgerUp
  deriving DecidableEq

def closedNormalEndpointLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalEndpointLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalEndpointLedgerEncodeBHist h

def closedNormalEndpointLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalEndpointLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalEndpointLedgerDecodeBHist tail)

private theorem closedNormalEndpointLedger_decode_encode_bhist :
    ∀ h : BHist,
      closedNormalEndpointLedgerDecodeBHist (closedNormalEndpointLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedNormalEndpointLedgerToEventFlow :
    ClosedNormalEndpointLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalEndpointLedgerUp.mk typed closed beta falseRow route transport
      continuation provenance nameCert =>
      [[BMark.b0],
        closedNormalEndpointLedgerEncodeBHist typed,
        [BMark.b1, BMark.b0],
        closedNormalEndpointLedgerEncodeBHist closed,
        [BMark.b1, BMark.b1, BMark.b0],
        closedNormalEndpointLedgerEncodeBHist beta,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalEndpointLedgerEncodeBHist falseRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalEndpointLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalEndpointLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalEndpointLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedNormalEndpointLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedNormalEndpointLedgerEncodeBHist nameCert]

def closedNormalEndpointLedgerFromEventFlow :
    EventFlow → Option ClosedNormalEndpointLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | typed :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | beta :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | falseRow :: rest7 =>
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
                                                                                (ClosedNormalEndpointLedgerUp.mk
                                                                                  (closedNormalEndpointLedgerDecodeBHist typed)
                                                                                  (closedNormalEndpointLedgerDecodeBHist closed)
                                                                                  (closedNormalEndpointLedgerDecodeBHist beta)
                                                                                  (closedNormalEndpointLedgerDecodeBHist falseRow)
                                                                                  (closedNormalEndpointLedgerDecodeBHist route)
                                                                                  (closedNormalEndpointLedgerDecodeBHist transport)
                                                                                  (closedNormalEndpointLedgerDecodeBHist continuation)
                                                                                  (closedNormalEndpointLedgerDecodeBHist provenance)
                                                                                  (closedNormalEndpointLedgerDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem closedNormalEndpointLedger_round_trip :
    ∀ x : ClosedNormalEndpointLedgerUp,
      closedNormalEndpointLedgerFromEventFlow
        (closedNormalEndpointLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typed closed beta falseRow route transport continuation provenance nameCert =>
      change
        some
          (ClosedNormalEndpointLedgerUp.mk
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist typed))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist closed))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist beta))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist falseRow))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist route))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist transport))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist continuation))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist provenance))
            (closedNormalEndpointLedgerDecodeBHist
              (closedNormalEndpointLedgerEncodeBHist nameCert))) =
          some
            (ClosedNormalEndpointLedgerUp.mk typed closed beta falseRow route transport
              continuation provenance nameCert)
      rw [closedNormalEndpointLedger_decode_encode_bhist typed,
        closedNormalEndpointLedger_decode_encode_bhist closed,
        closedNormalEndpointLedger_decode_encode_bhist beta,
        closedNormalEndpointLedger_decode_encode_bhist falseRow,
        closedNormalEndpointLedger_decode_encode_bhist route,
        closedNormalEndpointLedger_decode_encode_bhist transport,
        closedNormalEndpointLedger_decode_encode_bhist continuation,
        closedNormalEndpointLedger_decode_encode_bhist provenance,
        closedNormalEndpointLedger_decode_encode_bhist nameCert]

private theorem closedNormalEndpointLedgerToEventFlow_injective
    {x y : ClosedNormalEndpointLedgerUp} :
    closedNormalEndpointLedgerToEventFlow x =
      closedNormalEndpointLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalEndpointLedgerFromEventFlow
          (closedNormalEndpointLedgerToEventFlow x) =
        closedNormalEndpointLedgerFromEventFlow
          (closedNormalEndpointLedgerToEventFlow y) :=
    congrArg closedNormalEndpointLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedNormalEndpointLedger_round_trip x).symm
      (Eq.trans hread (closedNormalEndpointLedger_round_trip y)))

instance closedNormalEndpointLedgerBHistCarrier :
    BHistCarrier ClosedNormalEndpointLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalEndpointLedgerToEventFlow
  fromEventFlow := closedNormalEndpointLedgerFromEventFlow

instance closedNormalEndpointLedgerChapterTasteGate :
    ChapterTasteGate ClosedNormalEndpointLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedNormalEndpointLedgerFromEventFlow
          (closedNormalEndpointLedgerToEventFlow x) =
        some x
    exact closedNormalEndpointLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedNormalEndpointLedgerToEventFlow_injective heq)

instance closedNormalEndpointLedgerFieldFaithful :
    FieldFaithful ClosedNormalEndpointLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosedNormalEndpointLedgerUp.mk typed closed beta falseRow route transport
        continuation provenance nameCert =>
        [typed, closed, beta, falseRow, route, transport, continuation, provenance,
          nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk typed1 closed1 beta1 falseRow1 route1 transport1 continuation1 provenance1
        nameCert1 =>
        cases y with
        | mk typed2 closed2 beta2 falseRow2 route2 transport2 continuation2 provenance2
            nameCert2 =>
            injection h with hTyped t1
            injection t1 with hClosed t2
            injection t2 with hBeta t3
            injection t3 with hFalse t4
            injection t4 with hRoute t5
            injection t5 with hTransport t6
            injection t6 with hContinuation t7
            injection t7 with hProvenance t8
            injection t8 with hNameCert _
            cases hTyped
            cases hClosed
            cases hBeta
            cases hFalse
            cases hRoute
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hNameCert
            rfl

theorem ClosedNormalEndpointLedgerTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ClosedNormalEndpointLedgerUp) ∧
      Nonempty (ChapterTasteGate ClosedNormalEndpointLedgerUp) ∧
        closedNormalEndpointLedgerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
          closedNormalEndpointLedgerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨closedNormalEndpointLedgerBHistCarrier⟩
  · constructor
    · exact ⟨closedNormalEndpointLedgerChapterTasteGate⟩
    · constructor
      · rfl
      · rfl

end BEDC.Derived.ClosedNormalEndpointLedgerUp
