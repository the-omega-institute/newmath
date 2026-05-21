import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastConvergentSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastConvergentSeriesUp : Type where
  | mk :
      (series seq partialSums fastSchedule tailLedger regReadback realSeal transports routes
        provenance nameCert : BHist) →
      FastConvergentSeriesUp
  deriving DecidableEq

def FastConvergentSeriesTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b1]

def FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist h

def FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist
          (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist h) =
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

def FastConvergentSeriesTasteGate_single_carrier_alignment_fields :
    FastConvergentSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastConvergentSeriesUp.mk series seq partialSums fastSchedule tailLedger regReadback
      realSeal transports routes provenance nameCert =>
      [series, seq, partialSums, fastSchedule, tailLedger, regReadback, realSeal,
        transports, routes, provenance, nameCert]

def FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow :
    FastConvergentSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FastConvergentSeriesUp.mk series seq partialSums fastSchedule tailLedger regReadback
      realSeal transports routes provenance nameCert =>
      [FastConvergentSeriesTasteGate_single_carrier_alignment_tag,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist series,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist seq,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist partialSums,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist fastSchedule,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist tailLedger,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist regReadback,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist realSeal,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist transports,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist routes,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist provenance,
        FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist nameCert]

private def FastConvergentSeriesTasteGate_single_carrier_alignment_decodePacket
    (series seq partialSums fastSchedule tailLedger regReadback realSeal transports routes
      provenance nameCert : RawEvent) : FastConvergentSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FastConvergentSeriesUp.mk
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist series)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist seq)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist partialSums)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist fastSchedule)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist tailLedger)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist regReadback)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist realSeal)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist transports)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist routes)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist provenance)
    (FastConvergentSeriesTasteGate_single_carrier_alignment_decodeBHist nameCert)

def FastConvergentSeriesTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option FastConvergentSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | tag :: rest0 =>
      match tag with
      | [BMark.b1, BMark.b0, BMark.b1, BMark.b1] =>
          match rest0 with
          | [] => none
          | series :: rest1 =>
              match rest1 with
              | [] => none
              | seq :: rest2 =>
                  match rest2 with
                  | [] => none
                  | partialSums :: rest3 =>
                      match rest3 with
                      | [] => none
                      | fastSchedule :: rest4 =>
                          match rest4 with
                          | [] => none
                          | tailLedger :: rest5 =>
                              match rest5 with
                              | [] => none
                              | regReadback :: rest6 =>
                                  match rest6 with
                                  | [] => none
                                  | realSeal :: rest7 =>
                                      match rest7 with
                                      | [] => none
                                      | transports :: rest8 =>
                                          match rest8 with
                                          | [] => none
                                          | routes :: rest9 =>
                                              match rest9 with
                                              | [] => none
                                              | provenance :: rest10 =>
                                                  match rest10 with
                                                  | [] => none
                                                  | nameCert :: rest11 =>
                                                      match rest11 with
                                                      | [] =>
                                                          some
                                                            (FastConvergentSeriesTasteGate_single_carrier_alignment_decodePacket
                                                              series seq partialSums
                                                              fastSchedule tailLedger
                                                              regReadback realSeal transports
                                                              routes provenance nameCert)
                                                      | _ :: _ => none
      | _ => none

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_mk_congr
    {series series' seq seq' partialSums partialSums' fastSchedule fastSchedule'
      tailLedger tailLedger' regReadback regReadback' realSeal realSeal' transports
      transports' routes routes' provenance provenance' nameCert nameCert' : BHist}
    (hSeries : series' = series)
    (hSeq : seq' = seq)
    (hPartialSums : partialSums' = partialSums)
    (hFastSchedule : fastSchedule' = fastSchedule)
    (hTailLedger : tailLedger' = tailLedger)
    (hRegReadback : regReadback' = regReadback)
    (hRealSeal : realSeal' = realSeal)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    FastConvergentSeriesUp.mk series' seq' partialSums' fastSchedule' tailLedger'
        regReadback' realSeal' transports' routes' provenance' nameCert' =
      FastConvergentSeriesUp.mk series seq partialSums fastSchedule tailLedger regReadback
        realSeal transports routes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSeries
  cases hSeq
  cases hPartialSums
  cases hFastSchedule
  cases hTailLedger
  cases hRegReadback
  cases hRealSeal
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FastConvergentSeriesUp,
      FastConvergentSeriesTasteGate_single_carrier_alignment_fromEventFlow
          (FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk series seq partialSums fastSchedule tailLedger regReadback realSeal transports routes
      provenance nameCert =>
      change
        some
          (FastConvergentSeriesTasteGate_single_carrier_alignment_decodePacket
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist series)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist seq)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist partialSums)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist fastSchedule)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist tailLedger)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist regReadback)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist realSeal)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist transports)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist routes)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist provenance)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist nameCert)) =
          some
            (FastConvergentSeriesUp.mk series seq partialSums fastSchedule tailLedger
              regReadback realSeal transports routes provenance nameCert)
      unfold FastConvergentSeriesTasteGate_single_carrier_alignment_decodePacket
      exact
        congrArg some
          (FastConvergentSeriesTasteGate_single_carrier_alignment_mk_congr
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode series)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode seq)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode partialSums)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode fastSchedule)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode tailLedger)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode regReadback)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode realSeal)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode transports)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode routes)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode provenance)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode nameCert))

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FastConvergentSeriesUp} :
    FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow x =
        FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FastConvergentSeriesTasteGate_single_carrier_alignment_fromEventFlow
          (FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow x) =
        FastConvergentSeriesTasteGate_single_carrier_alignment_fromEventFlow
          (FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FastConvergentSeriesTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip y)))

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FastConvergentSeriesUp,
      FastConvergentSeriesTasteGate_single_carrier_alignment_fields x =
          FastConvergentSeriesTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk series seq partialSums fastSchedule tailLedger regReadback realSeal transports routes
      provenance nameCert =>
      cases y with
      | mk series' seq' partialSums' fastSchedule' tailLedger' regReadback' realSeal'
          transports' routes' provenance' nameCert' =>
          cases hfields
          rfl

instance FastConvergentSeriesTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier FastConvergentSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FastConvergentSeriesTasteGate_single_carrier_alignment_fromEventFlow

instance FastConvergentSeriesTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate FastConvergentSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FastConvergentSeriesTasteGate_single_carrier_alignment_fromEventFlow
          (FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance FastConvergentSeriesTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful FastConvergentSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := FastConvergentSeriesTasteGate_single_carrier_alignment_fields
  field_faithful := FastConvergentSeriesTasteGate_single_carrier_alignment_fields_faithful

instance FastConvergentSeriesTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial FastConvergentSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FastConvergentSeriesUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FastConvergentSeriesUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FastConvergentSeriesTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FastConvergentSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FastConvergentSeriesTasteGate_single_carrier_alignment_ChapterTasteGate

theorem FastConvergentSeriesTasteGate_single_carrier_alignment :
    FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist BHist.Empty = [] ∧
      FastConvergentSeriesTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] ∧
        ∀ A S Q mu T R E L C P N : BHist,
          FastConvergentSeriesTasteGate_single_carrier_alignment_fields
              (FastConvergentSeriesUp.mk A S Q mu T R E L C P N) =
            [A, S, Q, mu, T, R, E, L, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · intro A S Q mu T R E L C P N
      rfl

end BEDC.Derived.FastConvergentSeriesUp
