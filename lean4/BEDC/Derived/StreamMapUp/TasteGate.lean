import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamMapUp : Type where
  | mk (source target pointMap output tail ledger realSeal transport replay provenance name :
      BHist) : StreamMapUp
  deriving DecidableEq

def streamMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamMapEncodeBHist h

def streamMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamMapDecodeBHist tail)

private theorem streamMapDecode_encode_bhist :
    ∀ h : BHist, streamMapDecodeBHist (streamMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def streamMapToEventFlow : StreamMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StreamMapUp.mk source target pointMap output tail ledger realSeal transport replay provenance
      name =>
      [streamMapEncodeBHist source,
        streamMapEncodeBHist target,
        streamMapEncodeBHist pointMap,
        streamMapEncodeBHist output,
        streamMapEncodeBHist tail,
        streamMapEncodeBHist ledger,
        streamMapEncodeBHist realSeal,
        streamMapEncodeBHist transport,
        streamMapEncodeBHist replay,
        streamMapEncodeBHist provenance,
        streamMapEncodeBHist name]

def streamMapFromEventFlow : EventFlow → Option StreamMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | pointMap :: rest2 =>
              match rest2 with
              | [] => none
              | output :: rest3 =>
                  match rest3 with
                  | [] => none
                  | tail :: rest4 =>
                      match rest4 with
                      | [] => none
                      | ledger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | name :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (StreamMapUp.mk
                                                      (streamMapDecodeBHist source)
                                                      (streamMapDecodeBHist target)
                                                      (streamMapDecodeBHist pointMap)
                                                      (streamMapDecodeBHist output)
                                                      (streamMapDecodeBHist tail)
                                                      (streamMapDecodeBHist ledger)
                                                      (streamMapDecodeBHist realSeal)
                                                      (streamMapDecodeBHist transport)
                                                      (streamMapDecodeBHist replay)
                                                      (streamMapDecodeBHist provenance)
                                                      (streamMapDecodeBHist name))
                                              | _ :: _ => none

private theorem streamMap_round_trip :
    ∀ x : StreamMapUp, streamMapFromEventFlow (streamMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target pointMap output tail ledger realSeal transport replay provenance name =>
      change
        some
          (StreamMapUp.mk
            (streamMapDecodeBHist (streamMapEncodeBHist source))
            (streamMapDecodeBHist (streamMapEncodeBHist target))
            (streamMapDecodeBHist (streamMapEncodeBHist pointMap))
            (streamMapDecodeBHist (streamMapEncodeBHist output))
            (streamMapDecodeBHist (streamMapEncodeBHist tail))
            (streamMapDecodeBHist (streamMapEncodeBHist ledger))
            (streamMapDecodeBHist (streamMapEncodeBHist realSeal))
            (streamMapDecodeBHist (streamMapEncodeBHist transport))
            (streamMapDecodeBHist (streamMapEncodeBHist replay))
            (streamMapDecodeBHist (streamMapEncodeBHist provenance))
            (streamMapDecodeBHist (streamMapEncodeBHist name))) =
          some
            (StreamMapUp.mk source target pointMap output tail ledger realSeal transport replay
              provenance name)
      rw [streamMapDecode_encode_bhist source,
        streamMapDecode_encode_bhist target,
        streamMapDecode_encode_bhist pointMap,
        streamMapDecode_encode_bhist output,
        streamMapDecode_encode_bhist tail,
        streamMapDecode_encode_bhist ledger,
        streamMapDecode_encode_bhist realSeal,
        streamMapDecode_encode_bhist transport,
        streamMapDecode_encode_bhist replay,
        streamMapDecode_encode_bhist provenance,
        streamMapDecode_encode_bhist name]

private theorem StreamMapToEventFlow_injective {x y : StreamMapUp} :
    streamMapToEventFlow x = streamMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamMapFromEventFlow (streamMapToEventFlow x) =
        streamMapFromEventFlow (streamMapToEventFlow y) :=
    congrArg streamMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (streamMap_round_trip x).symm (Eq.trans hread (streamMap_round_trip y)))

instance streamMapBHistCarrier : BHistCarrier StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamMapToEventFlow
  fromEventFlow := streamMapFromEventFlow

instance streamMapChapterTasteGate : ChapterTasteGate StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamMapFromEventFlow (streamMapToEventFlow x) = some x
    exact streamMap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StreamMapToEventFlow_injective heq)

instance streamMapNontrivial : Nontrivial StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StreamMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamMapChapterTasteGate

theorem StreamMapTasteGate_single_carrier_alignment :
    (forall h : BHist, streamMapDecodeBHist (streamMapEncodeBHist h) = h) /\
      (forall x : StreamMapUp, streamMapFromEventFlow (streamMapToEventFlow x) = some x) /\
      (forall x y : StreamMapUp, streamMapToEventFlow x = streamMapToEventFlow y -> x = y) /\
      streamMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact streamMapDecode_encode_bhist
  · constructor
    · exact streamMap_round_trip
    · constructor
      · intro x y h
        exact StreamMapToEventFlow_injective h
      · rfl

end BEDC.Derived.StreamMapUp
