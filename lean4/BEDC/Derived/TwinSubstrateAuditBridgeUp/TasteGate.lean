import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TwinSubstrateAuditBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TwinSubstrateAuditBridgeUp : Type where
  | mk : (metacic ground alignment refusal transport continuation provenance name : BHist) →
      TwinSubstrateAuditBridgeUp
  deriving DecidableEq

def twinSubstrateAuditBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: twinSubstrateAuditBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: twinSubstrateAuditBridgeEncodeBHist h

def twinSubstrateAuditBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (twinSubstrateAuditBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (twinSubstrateAuditBridgeDecodeBHist tail)

private theorem twinSubstrateAuditBridgeDecode_encode_bhist :
    ∀ h : BHist,
      twinSubstrateAuditBridgeDecodeBHist (twinSubstrateAuditBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem twinSubstrateAuditBridge_mk_congr
    {metacic metacic' ground ground' alignment alignment' refusal refusal' transport transport'
      continuation continuation' provenance provenance' name name' : BHist}
    (hMetaCIC : metacic' = metacic)
    (hGround : ground' = ground)
    (hAlignment : alignment' = alignment)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    TwinSubstrateAuditBridgeUp.mk metacic' ground' alignment' refusal' transport'
        continuation' provenance' name' =
      TwinSubstrateAuditBridgeUp.mk metacic ground alignment refusal transport continuation
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMetaCIC
  cases hGround
  cases hAlignment
  cases hRefusal
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def twinSubstrateAuditBridgeToEventFlow : TwinSubstrateAuditBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TwinSubstrateAuditBridgeUp.mk metacic ground alignment refusal transport continuation
      provenance name =>
      [[BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist metacic,
        [BMark.b1, BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist ground,
        [BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist alignment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        twinSubstrateAuditBridgeEncodeBHist name]

def twinSubstrateAuditBridgeFromEventFlow :
    EventFlow → Option TwinSubstrateAuditBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metacic :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | ground :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | alignment :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusal :: rest7 =>
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
                                              | continuation :: rest11 =>
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
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (TwinSubstrateAuditBridgeUp.mk
                                                                          (twinSubstrateAuditBridgeDecodeBHist metacic)
                                                                          (twinSubstrateAuditBridgeDecodeBHist ground)
                                                                          (twinSubstrateAuditBridgeDecodeBHist alignment)
                                                                          (twinSubstrateAuditBridgeDecodeBHist refusal)
                                                                          (twinSubstrateAuditBridgeDecodeBHist transport)
                                                                          (twinSubstrateAuditBridgeDecodeBHist continuation)
                                                                          (twinSubstrateAuditBridgeDecodeBHist provenance)
                                                                          (twinSubstrateAuditBridgeDecodeBHist name))
                                                                  | _ :: _ => none

private theorem twinSubstrateAuditBridge_round_trip :
    ∀ x : TwinSubstrateAuditBridgeUp,
      twinSubstrateAuditBridgeFromEventFlow (twinSubstrateAuditBridgeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metacic ground alignment refusal transport continuation provenance name =>
      change
        some
          (TwinSubstrateAuditBridgeUp.mk
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist metacic))
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist ground))
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist alignment))
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist refusal))
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist transport))
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist continuation))
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist provenance))
            (twinSubstrateAuditBridgeDecodeBHist
              (twinSubstrateAuditBridgeEncodeBHist name))) =
          some
            (TwinSubstrateAuditBridgeUp.mk metacic ground alignment refusal transport
              continuation provenance name)
      exact
        congrArg some
          (twinSubstrateAuditBridge_mk_congr
            (twinSubstrateAuditBridgeDecode_encode_bhist metacic)
            (twinSubstrateAuditBridgeDecode_encode_bhist ground)
            (twinSubstrateAuditBridgeDecode_encode_bhist alignment)
            (twinSubstrateAuditBridgeDecode_encode_bhist refusal)
            (twinSubstrateAuditBridgeDecode_encode_bhist transport)
            (twinSubstrateAuditBridgeDecode_encode_bhist continuation)
            (twinSubstrateAuditBridgeDecode_encode_bhist provenance)
            (twinSubstrateAuditBridgeDecode_encode_bhist name))

private theorem twinSubstrateAuditBridgeToEventFlow_injective
    {x y : TwinSubstrateAuditBridgeUp} :
    twinSubstrateAuditBridgeToEventFlow x = twinSubstrateAuditBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      twinSubstrateAuditBridgeFromEventFlow (twinSubstrateAuditBridgeToEventFlow x) =
        twinSubstrateAuditBridgeFromEventFlow (twinSubstrateAuditBridgeToEventFlow y) :=
    congrArg twinSubstrateAuditBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (twinSubstrateAuditBridge_round_trip x).symm
      (Eq.trans hread (twinSubstrateAuditBridge_round_trip y)))

instance twinSubstrateAuditBridgeBHistCarrier :
    BHistCarrier TwinSubstrateAuditBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := twinSubstrateAuditBridgeToEventFlow
  fromEventFlow := twinSubstrateAuditBridgeFromEventFlow

instance twinSubstrateAuditBridgeChapterTasteGate :
    ChapterTasteGate TwinSubstrateAuditBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change twinSubstrateAuditBridgeFromEventFlow (twinSubstrateAuditBridgeToEventFlow x) =
      some x
    exact twinSubstrateAuditBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (twinSubstrateAuditBridgeToEventFlow_injective heq)

instance twinSubstrateAuditBridgeFieldFaithful :
    FieldFaithful TwinSubstrateAuditBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TwinSubstrateAuditBridgeUp.mk metacic ground alignment refusal transport continuation
        provenance name =>
        [metacic, ground, alignment, refusal, transport, continuation, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk metacic1 ground1 alignment1 refusal1 transport1 continuation1 provenance1 name1 =>
        cases y with
        | mk metacic2 ground2 alignment2 refusal2 transport2 continuation2 provenance2 name2 =>
            injection h with hMetaCIC t1
            injection t1 with hGround t2
            injection t2 with hAlignment t3
            injection t3 with hRefusal t4
            injection t4 with hTransport t5
            injection t5 with hContinuation t6
            injection t6 with hProvenance t7
            injection t7 with hName _
            cases hMetaCIC
            cases hGround
            cases hAlignment
            cases hRefusal
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hName
            rfl

instance twinSubstrateAuditBridgeNontrivial :
    Nontrivial TwinSubstrateAuditBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TwinSubstrateAuditBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TwinSubstrateAuditBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TwinSubstrateAuditBridgeTasteGate_single_carrier_alignment :
    (forall h : BHist,
        twinSubstrateAuditBridgeDecodeBHist (twinSubstrateAuditBridgeEncodeBHist h) = h) /\
      (forall x : TwinSubstrateAuditBridgeUp,
        twinSubstrateAuditBridgeFromEventFlow (twinSubstrateAuditBridgeToEventFlow x) =
          some x) /\
      (forall x y : TwinSubstrateAuditBridgeUp,
        twinSubstrateAuditBridgeToEventFlow x =
          twinSubstrateAuditBridgeToEventFlow y -> x = y) /\
      twinSubstrateAuditBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact twinSubstrateAuditBridgeDecode_encode_bhist
  · constructor
    · exact twinSubstrateAuditBridge_round_trip
    · constructor
      · intro x y heq
        exact twinSubstrateAuditBridgeToEventFlow_injective heq
      · rfl

end BEDC.Derived.TwinSubstrateAuditBridgeUp
