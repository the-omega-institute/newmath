import BEDC.Derived.FastConvergentSeriesUp
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
      (series seq partialSums schedule tailLedger regReadback realSeal transports routes
        provenance localName : BHist) →
        FastConvergentSeriesUp
  deriving DecidableEq

def fastConvergentSeriesTasteGate_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b0]

def fastConvergentSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastConvergentSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastConvergentSeriesEncodeBHist h

def fastConvergentSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastConvergentSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastConvergentSeriesDecodeBHist tail)

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_mk_congr
    {series series' seq seq' partialSums partialSums' schedule schedule' tailLedger
      tailLedger' regReadback regReadback' realSeal realSeal' transports transports' routes
      routes' provenance provenance' localName localName' : BHist}
    (hSeries : series' = series)
    (hSeq : seq' = seq)
    (hPartialSums : partialSums' = partialSums)
    (hSchedule : schedule' = schedule)
    (hTailLedger : tailLedger' = tailLedger)
    (hRegReadback : regReadback' = regReadback)
    (hRealSeal : realSeal' = realSeal)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    FastConvergentSeriesUp.mk series' seq' partialSums' schedule' tailLedger' regReadback'
        realSeal' transports' routes' provenance' localName' =
      FastConvergentSeriesUp.mk series seq partialSums schedule tailLedger regReadback realSeal
        transports routes provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSeries
  cases hSeq
  cases hPartialSums
  cases hSchedule
  cases hTailLedger
  cases hRegReadback
  cases hRealSeal
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hLocalName
  rfl

def fastConvergentSeriesFields : FastConvergentSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastConvergentSeriesUp.mk series seq partialSums schedule tailLedger regReadback
      realSeal transports routes provenance localName =>
      [series, seq, partialSums, schedule, tailLedger, regReadback, realSeal, transports,
        routes, provenance, localName]

def fastConvergentSeriesToEventFlow : FastConvergentSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FastConvergentSeriesUp.mk series seq partialSums schedule tailLedger regReadback
      realSeal transports routes provenance localName =>
      [fastConvergentSeriesTasteGate_tag,
        fastConvergentSeriesEncodeBHist series,
        fastConvergentSeriesEncodeBHist seq,
        fastConvergentSeriesEncodeBHist partialSums,
        fastConvergentSeriesEncodeBHist schedule,
        fastConvergentSeriesEncodeBHist tailLedger,
        fastConvergentSeriesEncodeBHist regReadback,
        fastConvergentSeriesEncodeBHist realSeal,
        fastConvergentSeriesEncodeBHist transports,
        fastConvergentSeriesEncodeBHist routes,
        fastConvergentSeriesEncodeBHist provenance,
        fastConvergentSeriesEncodeBHist localName]

def fastConvergentSeriesFromEventFlow : EventFlow → Option FastConvergentSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
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
                  | schedule :: rest4 =>
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
                                              | localName :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (FastConvergentSeriesUp.mk
                                                          (fastConvergentSeriesDecodeBHist series)
                                                          (fastConvergentSeriesDecodeBHist seq)
                                                          (fastConvergentSeriesDecodeBHist
                                                            partialSums)
                                                          (fastConvergentSeriesDecodeBHist
                                                            schedule)
                                                          (fastConvergentSeriesDecodeBHist
                                                            tailLedger)
                                                          (fastConvergentSeriesDecodeBHist
                                                            regReadback)
                                                          (fastConvergentSeriesDecodeBHist realSeal)
                                                          (fastConvergentSeriesDecodeBHist
                                                            transports)
                                                          (fastConvergentSeriesDecodeBHist routes)
                                                          (fastConvergentSeriesDecodeBHist
                                                            provenance)
                                                          (fastConvergentSeriesDecodeBHist
                                                            localName))
                                                  | _ :: _ => none

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FastConvergentSeriesUp,
      fastConvergentSeriesFromEventFlow (fastConvergentSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk series seq partialSums schedule tailLedger regReadback realSeal transports routes
      provenance localName =>
      change
        some
          (FastConvergentSeriesUp.mk
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist series))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist seq))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist partialSums))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist schedule))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist tailLedger))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist regReadback))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist realSeal))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist transports))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist routes))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist provenance))
            (fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist localName))) =
          some
            (FastConvergentSeriesUp.mk series seq partialSums schedule tailLedger regReadback
              realSeal transports routes provenance localName)
      exact
        congrArg some
          (FastConvergentSeriesTasteGate_single_carrier_alignment_mk_congr
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode series)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode seq)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode partialSums)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode schedule)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode tailLedger)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode regReadback)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode realSeal)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode transports)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode routes)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode provenance)
            (FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode localName))

private theorem FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FastConvergentSeriesUp} :
    fastConvergentSeriesToEventFlow x = fastConvergentSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastConvergentSeriesFromEventFlow (fastConvergentSeriesToEventFlow x) =
        fastConvergentSeriesFromEventFlow (fastConvergentSeriesToEventFlow y) :=
    congrArg fastConvergentSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip y)))

instance FastConvergentSeriesTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier FastConvergentSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastConvergentSeriesToEventFlow
  fromEventFlow := fastConvergentSeriesFromEventFlow

instance FastConvergentSeriesTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate FastConvergentSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastConvergentSeriesFromEventFlow (fastConvergentSeriesToEventFlow x) = some x
    exact FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def FastConvergentSeriesTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FastConvergentSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FastConvergentSeriesTasteGate_single_carrier_alignment_ChapterTasteGate

theorem FastConvergentSeriesTasteGate_single_carrier_alignment :
    (fastConvergentSeriesTasteGate_tag = [BMark.b0]) ∧
      (∀ h : BHist, fastConvergentSeriesDecodeBHist (fastConvergentSeriesEncodeBHist h) = h) ∧
        (∀ x : FastConvergentSeriesUp,
          fastConvergentSeriesFromEventFlow (fastConvergentSeriesToEventFlow x) = some x) ∧
          (∀ {x y : FastConvergentSeriesUp},
            fastConvergentSeriesToEventFlow x = fastConvergentSeriesToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact FastConvergentSeriesTasteGate_single_carrier_alignment_decode_encode
    · constructor
      · exact FastConvergentSeriesTasteGate_single_carrier_alignment_round_trip
      · intro x y heq
        exact FastConvergentSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq

end BEDC.Derived.FastConvergentSeriesUp
