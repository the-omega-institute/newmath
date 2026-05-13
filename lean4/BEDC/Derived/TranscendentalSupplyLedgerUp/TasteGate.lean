import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TranscendentalSupplyLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TranscendentalSupplyLedgerUp : Type where
  | mk :
      (socketSite requestedSupply taxonomy auditGate transportRow routeRow provenanceRow
        nameCertRow : BHist) →
      TranscendentalSupplyLedgerUp
  deriving DecidableEq

def transcendentalSupplyLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: transcendentalSupplyLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: transcendentalSupplyLedgerEncodeBHist h

def transcendentalSupplyLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (transcendentalSupplyLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (transcendentalSupplyLedgerDecodeBHist tail)

private theorem transcendentalSupplyLedgerDecode_encode_bhist :
    ∀ h : BHist,
      transcendentalSupplyLedgerDecodeBHist (transcendentalSupplyLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem transcendentalSupplyLedger_mk_congr
    {socketSite socketSite' requestedSupply requestedSupply' taxonomy taxonomy'
      auditGate auditGate' transportRow transportRow' routeRow routeRow' provenanceRow
      provenanceRow' nameCertRow nameCertRow' : BHist}
    (hSocket : socketSite' = socketSite)
    (hRequested : requestedSupply' = requestedSupply)
    (hTaxonomy : taxonomy' = taxonomy)
    (hAudit : auditGate' = auditGate)
    (hTransport : transportRow' = transportRow)
    (hRoute : routeRow' = routeRow)
    (hProvenance : provenanceRow' = provenanceRow)
    (hNameCert : nameCertRow' = nameCertRow) :
    TranscendentalSupplyLedgerUp.mk socketSite' requestedSupply' taxonomy' auditGate'
        transportRow' routeRow' provenanceRow' nameCertRow' =
      TranscendentalSupplyLedgerUp.mk socketSite requestedSupply taxonomy auditGate
        transportRow routeRow provenanceRow nameCertRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSocket
  cases hRequested
  cases hTaxonomy
  cases hAudit
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

def transcendentalSupplyLedgerToEventFlow : TranscendentalSupplyLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TranscendentalSupplyLedgerUp.mk socketSite requestedSupply taxonomy auditGate transportRow
      routeRow provenanceRow nameCertRow =>
      [[BMark.b0],
        transcendentalSupplyLedgerEncodeBHist socketSite,
        [BMark.b1, BMark.b0],
        transcendentalSupplyLedgerEncodeBHist requestedSupply,
        [BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyLedgerEncodeBHist taxonomy,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyLedgerEncodeBHist auditGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyLedgerEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyLedgerEncodeBHist routeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyLedgerEncodeBHist provenanceRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        transcendentalSupplyLedgerEncodeBHist nameCertRow]

def transcendentalSupplyLedgerFromEventFlow :
    EventFlow → Option TranscendentalSupplyLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | socketSite :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | requestedSupply :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | taxonomy :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transportRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routeRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenanceRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCertRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (TranscendentalSupplyLedgerUp.mk
                                                                          (transcendentalSupplyLedgerDecodeBHist socketSite)
                                                                          (transcendentalSupplyLedgerDecodeBHist requestedSupply)
                                                                          (transcendentalSupplyLedgerDecodeBHist taxonomy)
                                                                          (transcendentalSupplyLedgerDecodeBHist auditGate)
                                                                          (transcendentalSupplyLedgerDecodeBHist transportRow)
                                                                          (transcendentalSupplyLedgerDecodeBHist routeRow)
                                                                          (transcendentalSupplyLedgerDecodeBHist provenanceRow)
                                                                          (transcendentalSupplyLedgerDecodeBHist nameCertRow))
                                                                  | _ :: _ => none

private theorem transcendentalSupplyLedger_round_trip :
    ∀ x : TranscendentalSupplyLedgerUp,
      transcendentalSupplyLedgerFromEventFlow (transcendentalSupplyLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk socketSite requestedSupply taxonomy auditGate transportRow routeRow provenanceRow
      nameCertRow =>
      change
        some
          (TranscendentalSupplyLedgerUp.mk
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist socketSite))
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist requestedSupply))
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist taxonomy))
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist auditGate))
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist transportRow))
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist routeRow))
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist provenanceRow))
            (transcendentalSupplyLedgerDecodeBHist
              (transcendentalSupplyLedgerEncodeBHist nameCertRow))) =
          some
            (TranscendentalSupplyLedgerUp.mk socketSite requestedSupply taxonomy auditGate
              transportRow routeRow provenanceRow nameCertRow)
      exact
        congrArg some
          (transcendentalSupplyLedger_mk_congr
            (transcendentalSupplyLedgerDecode_encode_bhist socketSite)
            (transcendentalSupplyLedgerDecode_encode_bhist requestedSupply)
            (transcendentalSupplyLedgerDecode_encode_bhist taxonomy)
            (transcendentalSupplyLedgerDecode_encode_bhist auditGate)
            (transcendentalSupplyLedgerDecode_encode_bhist transportRow)
            (transcendentalSupplyLedgerDecode_encode_bhist routeRow)
            (transcendentalSupplyLedgerDecode_encode_bhist provenanceRow)
            (transcendentalSupplyLedgerDecode_encode_bhist nameCertRow))

private theorem transcendentalSupplyLedgerToEventFlow_injective
    {x y : TranscendentalSupplyLedgerUp} :
    transcendentalSupplyLedgerToEventFlow x = transcendentalSupplyLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      transcendentalSupplyLedgerFromEventFlow (transcendentalSupplyLedgerToEventFlow x) =
        transcendentalSupplyLedgerFromEventFlow (transcendentalSupplyLedgerToEventFlow y) :=
    congrArg transcendentalSupplyLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (transcendentalSupplyLedger_round_trip x).symm
      (Eq.trans hread (transcendentalSupplyLedger_round_trip y)))

instance transcendentalSupplyLedgerBHistCarrier :
    BHistCarrier TranscendentalSupplyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := transcendentalSupplyLedgerToEventFlow
  fromEventFlow := transcendentalSupplyLedgerFromEventFlow

instance transcendentalSupplyLedgerChapterTasteGate :
    ChapterTasteGate TranscendentalSupplyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      transcendentalSupplyLedgerFromEventFlow (transcendentalSupplyLedgerToEventFlow x) =
        some x
    exact transcendentalSupplyLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (transcendentalSupplyLedgerToEventFlow_injective heq)

theorem TranscendentalSupplyLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      transcendentalSupplyLedgerDecodeBHist (transcendentalSupplyLedgerEncodeBHist h) = h) ∧
      (∀ x : TranscendentalSupplyLedgerUp,
        transcendentalSupplyLedgerFromEventFlow (transcendentalSupplyLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : TranscendentalSupplyLedgerUp,
          transcendentalSupplyLedgerToEventFlow x = transcendentalSupplyLedgerToEventFlow y →
            x = y) ∧
          transcendentalSupplyLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact transcendentalSupplyLedgerDecode_encode_bhist
  · constructor
    · exact transcendentalSupplyLedger_round_trip
    · constructor
      · intro x y heq
        exact transcendentalSupplyLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.TranscendentalSupplyLedgerUp
