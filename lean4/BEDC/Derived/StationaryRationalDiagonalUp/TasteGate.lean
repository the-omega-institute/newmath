import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StationaryRationalDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StationaryRationalDiagonalUp : Type where
  | mk :
      (rat constantStream regseq diagonal realSeal transport route provenance namecert
        endpoint : BHist) →
      StationaryRationalDiagonalUp
  deriving DecidableEq

def stationaryRationalDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stationaryRationalDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stationaryRationalDiagonalEncodeBHist h

def stationaryRationalDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stationaryRationalDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stationaryRationalDiagonalDecodeBHist tail)

private theorem stationaryRationalDiagonalDecode_encode_bhist :
    ∀ h : BHist,
      stationaryRationalDiagonalDecodeBHist (stationaryRationalDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stationaryRationalDiagonalToEventFlow : StationaryRationalDiagonalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StationaryRationalDiagonalUp.mk rat constantStream regseq diagonal realSeal transport route
      provenance namecert endpoint =>
      [[BMark.b0],
        stationaryRationalDiagonalEncodeBHist rat,
        [BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist constantStream,
        [BMark.b1, BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist regseq,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        stationaryRationalDiagonalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist namecert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        stationaryRationalDiagonalEncodeBHist endpoint]

def stationaryRationalDiagonalFromEventFlow
    (ef : EventFlow) : Option StationaryRationalDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | rat :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | constantStream :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regseq :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | diagonal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
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
                                                      | route :: rest13 =>
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
                                                                      | namecert ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | endpoint ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (StationaryRationalDiagonalUp.mk
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            rat)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            constantStream)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            regseq)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            diagonal)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            realSeal)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            transport)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            route)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            provenance)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            namecert)
                                                                                          (stationaryRationalDiagonalDecodeBHist
                                                                                            endpoint))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem StationaryRationalDiagonalTasteGate_single_carrier_alignment_mk_congr
    {rat rat' constantStream constantStream' regseq regseq' diagonal diagonal'
      realSeal realSeal' transport transport' route route' provenance provenance'
      namecert namecert' endpoint endpoint' : BHist} :
    rat = rat' →
      constantStream = constantStream' →
        regseq = regseq' →
          diagonal = diagonal' →
            realSeal = realSeal' →
              transport = transport' →
                route = route' →
                  provenance = provenance' →
                    namecert = namecert' →
                      endpoint = endpoint' →
                        StationaryRationalDiagonalUp.mk rat constantStream regseq diagonal
                            realSeal transport route provenance namecert endpoint =
                          StationaryRationalDiagonalUp.mk rat' constantStream' regseq'
                            diagonal' realSeal' transport' route' provenance' namecert'
                            endpoint' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hRat hConstantStream hRegseq hDiagonal hRealSeal hTransport hRoute hProvenance
    hNamecert hEndpoint
  cases hRat
  cases hConstantStream
  cases hRegseq
  cases hDiagonal
  cases hRealSeal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNamecert
  cases hEndpoint
  rfl

private theorem stationaryRationalDiagonal_round_trip :
    ∀ x : StationaryRationalDiagonalUp,
      stationaryRationalDiagonalFromEventFlow (stationaryRationalDiagonalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rat constantStream regseq diagonal realSeal transport route provenance namecert endpoint =>
      change
        some
          (StationaryRationalDiagonalUp.mk
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist rat))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist constantStream))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist regseq))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist diagonal))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist realSeal))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist transport))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist route))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist provenance))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist namecert))
            (stationaryRationalDiagonalDecodeBHist
              (stationaryRationalDiagonalEncodeBHist endpoint))) =
          some
            (StationaryRationalDiagonalUp.mk rat constantStream regseq diagonal realSeal
              transport route provenance namecert endpoint)
      have hRat := stationaryRationalDiagonalDecode_encode_bhist rat
      have hConstantStream := stationaryRationalDiagonalDecode_encode_bhist constantStream
      have hRegseq := stationaryRationalDiagonalDecode_encode_bhist regseq
      have hDiagonal := stationaryRationalDiagonalDecode_encode_bhist diagonal
      have hRealSeal := stationaryRationalDiagonalDecode_encode_bhist realSeal
      have hTransport := stationaryRationalDiagonalDecode_encode_bhist transport
      have hRoute := stationaryRationalDiagonalDecode_encode_bhist route
      have hProvenance := stationaryRationalDiagonalDecode_encode_bhist provenance
      have hNamecert := stationaryRationalDiagonalDecode_encode_bhist namecert
      have hEndpoint := stationaryRationalDiagonalDecode_encode_bhist endpoint
      exact congrArg some
        (StationaryRationalDiagonalTasteGate_single_carrier_alignment_mk_congr hRat
          hConstantStream hRegseq hDiagonal hRealSeal hTransport hRoute hProvenance
          hNamecert hEndpoint)

private theorem stationaryRationalDiagonalToEventFlow_injective
    {x y : StationaryRationalDiagonalUp} :
    stationaryRationalDiagonalToEventFlow x = stationaryRationalDiagonalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stationaryRationalDiagonalFromEventFlow (stationaryRationalDiagonalToEventFlow x) =
        stationaryRationalDiagonalFromEventFlow (stationaryRationalDiagonalToEventFlow y) :=
    congrArg stationaryRationalDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stationaryRationalDiagonal_round_trip x).symm
      (Eq.trans hread (stationaryRationalDiagonal_round_trip y)))

instance stationaryRationalDiagonalBHistCarrier :
    BHistCarrier StationaryRationalDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stationaryRationalDiagonalToEventFlow
  fromEventFlow := stationaryRationalDiagonalFromEventFlow

instance stationaryRationalDiagonalChapterTasteGate :
    ChapterTasteGate StationaryRationalDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stationaryRationalDiagonalFromEventFlow (stationaryRationalDiagonalToEventFlow x) =
      some x
    exact stationaryRationalDiagonal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stationaryRationalDiagonalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StationaryRationalDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stationaryRationalDiagonalChapterTasteGate

theorem StationaryRationalDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        stationaryRationalDiagonalDecodeBHist (stationaryRationalDiagonalEncodeBHist h) = h) ∧
      (∀ x : StationaryRationalDiagonalUp,
        stationaryRationalDiagonalFromEventFlow (stationaryRationalDiagonalToEventFlow x) =
          some x) ∧
        (∀ x y : StationaryRationalDiagonalUp,
          stationaryRationalDiagonalToEventFlow x = stationaryRationalDiagonalToEventFlow y →
            x = y) ∧
          stationaryRationalDiagonalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact stationaryRationalDiagonalDecode_encode_bhist
  · constructor
    · exact stationaryRationalDiagonal_round_trip
    · constructor
      · intro x y heq
        exact stationaryRationalDiagonalToEventFlow_injective heq
      · rfl

end BEDC.Derived.StationaryRationalDiagonalUp
