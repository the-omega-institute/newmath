import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ThueMorseStreamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ThueMorseStreamUp : Type where
  | mk :
      (index list stream automaton readback dyadic realSeal prefixTransport transport replay
        provenance localName : BHist) →
      ThueMorseStreamUp
  deriving DecidableEq

def thueMorseStreamEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: thueMorseStreamEncodeBHist h
  | BHist.e1 h => BMark.b1 :: thueMorseStreamEncodeBHist h

def thueMorseStreamDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (thueMorseStreamDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (thueMorseStreamDecodeBHist tail)

private theorem thueMorseStream_decode_encode_bhist :
    ∀ h : BHist, thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def thueMorseStreamFields : ThueMorseStreamUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ThueMorseStreamUp.mk index list stream automaton readback dyadic realSeal
      prefixTransport transport replay provenance localName =>
      [index, list, stream, automaton, readback, dyadic, realSeal, prefixTransport,
        transport, replay, provenance, localName]

def thueMorseStreamToEventFlow : ThueMorseStreamUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (thueMorseStreamFields x).map thueMorseStreamEncodeBHist

def thueMorseStreamFromEventFlow : EventFlow → Option ThueMorseStreamUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | index :: rest0 =>
      match rest0 with
      | [] => none
      | list :: rest1 =>
          match rest1 with
          | [] => none
          | stream :: rest2 =>
              match rest2 with
              | [] => none
              | automaton :: rest3 =>
                  match rest3 with
                  | [] => none
                  | readback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadic :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | prefixTransport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localName :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (ThueMorseStreamUp.mk
                                                          (thueMorseStreamDecodeBHist index)
                                                          (thueMorseStreamDecodeBHist list)
                                                          (thueMorseStreamDecodeBHist stream)
                                                          (thueMorseStreamDecodeBHist
                                                            automaton)
                                                          (thueMorseStreamDecodeBHist
                                                            readback)
                                                          (thueMorseStreamDecodeBHist dyadic)
                                                          (thueMorseStreamDecodeBHist
                                                            realSeal)
                                                          (thueMorseStreamDecodeBHist
                                                            prefixTransport)
                                                          (thueMorseStreamDecodeBHist
                                                            transport)
                                                          (thueMorseStreamDecodeBHist replay)
                                                          (thueMorseStreamDecodeBHist
                                                            provenance)
                                                          (thueMorseStreamDecodeBHist
                                                            localName))
                                                  | _ :: _ => none

private theorem thueMorseStream_round_trip :
    ∀ x : ThueMorseStreamUp,
      thueMorseStreamFromEventFlow (thueMorseStreamToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk index list stream automaton readback dyadic realSeal prefixTransport transport replay
      provenance localName =>
      change
        some
          (ThueMorseStreamUp.mk
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist index))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist list))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist stream))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist automaton))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist readback))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist dyadic))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist realSeal))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist prefixTransport))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist transport))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist replay))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist provenance))
            (thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist localName))) =
          some
            (ThueMorseStreamUp.mk index list stream automaton readback dyadic realSeal
              prefixTransport transport replay provenance localName)
      rw [thueMorseStream_decode_encode_bhist index,
        thueMorseStream_decode_encode_bhist list,
        thueMorseStream_decode_encode_bhist stream,
        thueMorseStream_decode_encode_bhist automaton,
        thueMorseStream_decode_encode_bhist readback,
        thueMorseStream_decode_encode_bhist dyadic,
        thueMorseStream_decode_encode_bhist realSeal,
        thueMorseStream_decode_encode_bhist prefixTransport,
        thueMorseStream_decode_encode_bhist transport,
        thueMorseStream_decode_encode_bhist replay,
        thueMorseStream_decode_encode_bhist provenance,
        thueMorseStream_decode_encode_bhist localName]

private theorem thueMorseStreamToEventFlow_injective {x y : ThueMorseStreamUp} :
    thueMorseStreamToEventFlow x = thueMorseStreamToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      thueMorseStreamFromEventFlow (thueMorseStreamToEventFlow x) =
        thueMorseStreamFromEventFlow (thueMorseStreamToEventFlow y) :=
    congrArg thueMorseStreamFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (thueMorseStream_round_trip x).symm
      (Eq.trans hread (thueMorseStream_round_trip y)))

instance thueMorseStreamBHistCarrier : BHistCarrier ThueMorseStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := thueMorseStreamToEventFlow
  fromEventFlow := thueMorseStreamFromEventFlow

instance thueMorseStreamChapterTasteGate : ChapterTasteGate ThueMorseStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change thueMorseStreamFromEventFlow (thueMorseStreamToEventFlow x) = some x
    exact thueMorseStream_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (thueMorseStreamToEventFlow_injective heq)

theorem ThueMorseStreamTasteGate_single_carrier_alignment :
    (∀ h : BHist, thueMorseStreamDecodeBHist (thueMorseStreamEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ThueMorseStreamUp) ∧
        Nonempty (ChapterTasteGate ThueMorseStreamUp) ∧
          thueMorseStreamEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact thueMorseStream_decode_encode_bhist
  · constructor
    · exact ⟨thueMorseStreamBHistCarrier⟩
    · constructor
      · exact ⟨thueMorseStreamChapterTasteGate⟩
      · rfl

end BEDC.Derived.ThueMorseStreamUp
