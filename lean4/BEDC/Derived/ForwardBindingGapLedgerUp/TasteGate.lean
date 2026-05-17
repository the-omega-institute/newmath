import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ForwardBindingGapLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ForwardBindingGapLedgerUp : Type where
  | mk
      (commitment record gapSocket refusalRow transport route provenance nameCert :
        BHist) :
      ForwardBindingGapLedgerUp
  deriving DecidableEq

def forwardBindingGapLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: forwardBindingGapLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: forwardBindingGapLedgerEncodeBHist h

def forwardBindingGapLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (forwardBindingGapLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (forwardBindingGapLedgerDecodeBHist tail)

private theorem forwardBindingGapLedgerDecode_encode_bhist :
    ∀ h : BHist,
      forwardBindingGapLedgerDecodeBHist
        (forwardBindingGapLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem forwardBindingGapLedger_mk_congr
    {commitment commitment' record record' gapSocket gapSocket' refusalRow
      refusalRow' transport transport' route route' provenance provenance'
      nameCert nameCert' : BHist}
    (hCommitment : commitment' = commitment)
    (hRecord : record' = record)
    (hGapSocket : gapSocket' = gapSocket)
    (hRefusalRow : refusalRow' = refusalRow)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    ForwardBindingGapLedgerUp.mk commitment' record' gapSocket' refusalRow'
        transport' route' provenance' nameCert' =
      ForwardBindingGapLedgerUp.mk commitment record gapSocket refusalRow
        transport route provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCommitment
  cases hRecord
  cases hGapSocket
  cases hRefusalRow
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

def forwardBindingGapLedgerToEventFlow :
    ForwardBindingGapLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ForwardBindingGapLedgerUp.mk commitment record gapSocket refusalRow
      transport route provenance nameCert =>
      [[BMark.b0],
        forwardBindingGapLedgerEncodeBHist commitment,
        [BMark.b1, BMark.b0],
        forwardBindingGapLedgerEncodeBHist record,
        [BMark.b1, BMark.b1, BMark.b0],
        forwardBindingGapLedgerEncodeBHist gapSocket,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forwardBindingGapLedgerEncodeBHist refusalRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forwardBindingGapLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forwardBindingGapLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        forwardBindingGapLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        forwardBindingGapLedgerEncodeBHist nameCert]

def forwardBindingGapLedgerFromEventFlow :
    EventFlow → Option ForwardBindingGapLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | commitment :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | record :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gapSocket :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusalRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ForwardBindingGapLedgerUp.mk
                                                                          (forwardBindingGapLedgerDecodeBHist commitment)
                                                                          (forwardBindingGapLedgerDecodeBHist record)
                                                                          (forwardBindingGapLedgerDecodeBHist gapSocket)
                                                                          (forwardBindingGapLedgerDecodeBHist refusalRow)
                                                                          (forwardBindingGapLedgerDecodeBHist transport)
                                                                          (forwardBindingGapLedgerDecodeBHist route)
                                                                          (forwardBindingGapLedgerDecodeBHist provenance)
                                                                          (forwardBindingGapLedgerDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem forwardBindingGapLedger_round_trip :
    ∀ x : ForwardBindingGapLedgerUp,
      forwardBindingGapLedgerFromEventFlow
        (forwardBindingGapLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk commitment record gapSocket refusalRow transport route provenance nameCert =>
      change
        some
          (ForwardBindingGapLedgerUp.mk
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist commitment))
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist record))
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist gapSocket))
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist refusalRow))
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist transport))
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist route))
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist provenance))
            (forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist nameCert))) =
          some
            (ForwardBindingGapLedgerUp.mk commitment record gapSocket refusalRow
              transport route provenance nameCert)
      exact
        congrArg some
          (forwardBindingGapLedger_mk_congr
            (forwardBindingGapLedgerDecode_encode_bhist commitment)
            (forwardBindingGapLedgerDecode_encode_bhist record)
            (forwardBindingGapLedgerDecode_encode_bhist gapSocket)
            (forwardBindingGapLedgerDecode_encode_bhist refusalRow)
            (forwardBindingGapLedgerDecode_encode_bhist transport)
            (forwardBindingGapLedgerDecode_encode_bhist route)
            (forwardBindingGapLedgerDecode_encode_bhist provenance)
            (forwardBindingGapLedgerDecode_encode_bhist nameCert))

theorem forwardBindingGapLedgerToEventFlow_injective
    {x y : ForwardBindingGapLedgerUp} :
    forwardBindingGapLedgerToEventFlow x =
      forwardBindingGapLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      forwardBindingGapLedgerFromEventFlow
          (forwardBindingGapLedgerToEventFlow x) =
        forwardBindingGapLedgerFromEventFlow
          (forwardBindingGapLedgerToEventFlow y) :=
    congrArg forwardBindingGapLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (forwardBindingGapLedger_round_trip x).symm
      (Eq.trans hread (forwardBindingGapLedger_round_trip y)))

instance forwardBindingGapLedgerBHistCarrier :
    BHistCarrier ForwardBindingGapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := forwardBindingGapLedgerToEventFlow
  fromEventFlow := forwardBindingGapLedgerFromEventFlow

instance forwardBindingGapLedgerChapterTasteGate :
    ChapterTasteGate ForwardBindingGapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      forwardBindingGapLedgerFromEventFlow
        (forwardBindingGapLedgerToEventFlow x) = some x
    exact forwardBindingGapLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (forwardBindingGapLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ForwardBindingGapLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  forwardBindingGapLedgerChapterTasteGate

instance forwardBindingGapLedgerFieldFaithful :
    FieldFaithful ForwardBindingGapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ForwardBindingGapLedgerUp.mk commitment record gapSocket refusalRow
        transport route provenance nameCert =>
        [commitment, record, gapSocket, refusalRow, transport, route, provenance,
          nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk commitment record gapSocket refusalRow transport route provenance nameCert =>
        cases y with
        | mk commitment' record' gapSocket' refusalRow' transport' route' provenance'
            nameCert' =>
            cases hfields
            rfl

instance forwardBindingGapLedgerNontrivial :
    Nontrivial ForwardBindingGapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ForwardBindingGapLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ForwardBindingGapLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ForwardBindingGapLedgerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ForwardBindingGapLedgerUp) ∧
      Nonempty (FieldFaithful ForwardBindingGapLedgerUp) ∧
        Nonempty (Nontrivial ForwardBindingGapLedgerUp) ∧
          (∀ h : BHist,
            forwardBindingGapLedgerDecodeBHist
              (forwardBindingGapLedgerEncodeBHist h) = h) ∧
            (∀ x : ForwardBindingGapLedgerUp,
              forwardBindingGapLedgerFromEventFlow
                (forwardBindingGapLedgerToEventFlow x) = some x) ∧
              (∀ x y : ForwardBindingGapLedgerUp,
                forwardBindingGapLedgerToEventFlow x =
                  forwardBindingGapLedgerToEventFlow y → x = y) ∧
                forwardBindingGapLedgerEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨forwardBindingGapLedgerChapterTasteGate⟩
  · constructor
    · exact ⟨forwardBindingGapLedgerFieldFaithful⟩
    · constructor
      · exact ⟨forwardBindingGapLedgerNontrivial⟩
      · constructor
        · exact forwardBindingGapLedgerDecode_encode_bhist
        · constructor
          · exact forwardBindingGapLedger_round_trip
          · constructor
            · intro x y heq
              exact forwardBindingGapLedgerToEventFlow_injective heq
            · rfl

end BEDC.Derived.ForwardBindingGapLedgerUp
