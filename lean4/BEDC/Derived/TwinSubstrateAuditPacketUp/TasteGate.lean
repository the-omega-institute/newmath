import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TwinSubstrateAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TwinSubstrateAuditPacketUp : Type where
  | mk :
      (groundCompiler metaCIC address boundary transport continuation provenance name :
        BHist) →
      TwinSubstrateAuditPacketUp
  deriving DecidableEq

def twinSubstrateAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: twinSubstrateAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: twinSubstrateAuditPacketEncodeBHist h

def twinSubstrateAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (twinSubstrateAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (twinSubstrateAuditPacketDecodeBHist tail)

private theorem twinSubstrateAuditPacketDecode_encode_bhist :
    ∀ h : BHist,
      twinSubstrateAuditPacketDecodeBHist
        (twinSubstrateAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem twinSubstrateAuditPacket_mk_congr
    {groundCompiler groundCompiler' metaCIC metaCIC' address address' boundary boundary'
      transport transport' continuation continuation' provenance provenance' name name' :
      BHist}
    (hGroundCompiler : groundCompiler' = groundCompiler)
    (hMetaCIC : metaCIC' = metaCIC)
    (hAddress : address' = address)
    (hBoundary : boundary' = boundary)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    TwinSubstrateAuditPacketUp.mk groundCompiler' metaCIC' address' boundary' transport'
        continuation' provenance' name' =
      TwinSubstrateAuditPacketUp.mk groundCompiler metaCIC address boundary transport
        continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGroundCompiler
  cases hMetaCIC
  cases hAddress
  cases hBoundary
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def twinSubstrateAuditPacketToEventFlow : TwinSubstrateAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TwinSubstrateAuditPacketUp.mk groundCompiler metaCIC address boundary transport
      continuation provenance name =>
      [[BMark.b0],
        twinSubstrateAuditPacketEncodeBHist groundCompiler,
        [BMark.b1, BMark.b0],
        twinSubstrateAuditPacketEncodeBHist metaCIC,
        [BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditPacketEncodeBHist address,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditPacketEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditPacketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditPacketEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditPacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        twinSubstrateAuditPacketEncodeBHist name]

def twinSubstrateAuditPacketFromEventFlow :
    EventFlow → Option TwinSubstrateAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | groundCompiler :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | metaCIC :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | address :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | boundary :: rest7 =>
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
                                                                        (TwinSubstrateAuditPacketUp.mk
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            groundCompiler)
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            metaCIC)
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            address)
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            boundary)
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            transport)
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            continuation)
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            provenance)
                                                                          (twinSubstrateAuditPacketDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem twinSubstrateAuditPacket_round_trip :
    ∀ x : TwinSubstrateAuditPacketUp,
      twinSubstrateAuditPacketFromEventFlow
        (twinSubstrateAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk groundCompiler metaCIC address boundary transport continuation provenance name =>
      change
        some
          (TwinSubstrateAuditPacketUp.mk
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist groundCompiler))
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist metaCIC))
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist address))
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist boundary))
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist transport))
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist continuation))
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist provenance))
            (twinSubstrateAuditPacketDecodeBHist
              (twinSubstrateAuditPacketEncodeBHist name))) =
          some
            (TwinSubstrateAuditPacketUp.mk groundCompiler metaCIC address boundary
              transport continuation provenance name)
      exact
        congrArg some
          (twinSubstrateAuditPacket_mk_congr
            (twinSubstrateAuditPacketDecode_encode_bhist groundCompiler)
            (twinSubstrateAuditPacketDecode_encode_bhist metaCIC)
            (twinSubstrateAuditPacketDecode_encode_bhist address)
            (twinSubstrateAuditPacketDecode_encode_bhist boundary)
            (twinSubstrateAuditPacketDecode_encode_bhist transport)
            (twinSubstrateAuditPacketDecode_encode_bhist continuation)
            (twinSubstrateAuditPacketDecode_encode_bhist provenance)
            (twinSubstrateAuditPacketDecode_encode_bhist name))

private theorem twinSubstrateAuditPacketToEventFlow_injective
    {x y : TwinSubstrateAuditPacketUp} :
    twinSubstrateAuditPacketToEventFlow x =
      twinSubstrateAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      twinSubstrateAuditPacketFromEventFlow
          (twinSubstrateAuditPacketToEventFlow x) =
        twinSubstrateAuditPacketFromEventFlow
          (twinSubstrateAuditPacketToEventFlow y) :=
    congrArg twinSubstrateAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (twinSubstrateAuditPacket_round_trip x).symm
      (Eq.trans hread (twinSubstrateAuditPacket_round_trip y)))

instance twinSubstrateAuditPacketBHistCarrier :
    BHistCarrier TwinSubstrateAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := twinSubstrateAuditPacketToEventFlow
  fromEventFlow := twinSubstrateAuditPacketFromEventFlow

instance twinSubstrateAuditPacketChapterTasteGate :
    ChapterTasteGate TwinSubstrateAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      twinSubstrateAuditPacketFromEventFlow
        (twinSubstrateAuditPacketToEventFlow x) = some x
    exact twinSubstrateAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (twinSubstrateAuditPacketToEventFlow_injective heq)

instance twinSubstrateAuditPacketFieldFaithful :
    FieldFaithful TwinSubstrateAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TwinSubstrateAuditPacketUp.mk groundCompiler metaCIC address boundary transport
        continuation provenance name =>
        [groundCompiler, metaCIC, address, boundary, transport, continuation, provenance,
          name]
  field_faithful := by
    intro x y h
    cases x with
    | mk groundCompiler₁ metaCIC₁ address₁ boundary₁ transport₁ continuation₁
        provenance₁ name₁ =>
        cases y with
        | mk groundCompiler₂ metaCIC₂ address₂ boundary₂ transport₂ continuation₂
            provenance₂ name₂ =>
            injection h with hGround hRest₁
            injection hRest₁ with hMetaCIC hRest₂
            injection hRest₂ with hAddress hRest₃
            injection hRest₃ with hBoundary hRest₄
            injection hRest₄ with hTransport hRest₅
            injection hRest₅ with hContinuation hRest₆
            injection hRest₆ with hProvenance hRest₇
            injection hRest₇ with hName _
            cases hGround
            cases hMetaCIC
            cases hAddress
            cases hBoundary
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hName
            rfl

instance twinSubstrateAuditPacketNontrivial :
    Nontrivial TwinSubstrateAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TwinSubstrateAuditPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TwinSubstrateAuditPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

namespace TasteGate

theorem TwinSubstrateAuditPacketTasteGate_single_carrier_alignment :
    (forall h : BHist,
        twinSubstrateAuditPacketDecodeBHist
          (twinSubstrateAuditPacketEncodeBHist h) = h) /\
      (forall x : TwinSubstrateAuditPacketUp,
        twinSubstrateAuditPacketFromEventFlow
          (twinSubstrateAuditPacketToEventFlow x) = some x) /\
      (forall x y : TwinSubstrateAuditPacketUp,
        twinSubstrateAuditPacketToEventFlow x =
          twinSubstrateAuditPacketToEventFlow y -> x = y) /\
      Nonempty (ChapterTasteGate TwinSubstrateAuditPacketUp) /\
      twinSubstrateAuditPacketEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact twinSubstrateAuditPacketDecode_encode_bhist
  · constructor
    · exact twinSubstrateAuditPacket_round_trip
    · constructor
      · intro x y heq
        exact twinSubstrateAuditPacketToEventFlow_injective heq
      · constructor
        · exact ⟨twinSubstrateAuditPacketChapterTasteGate⟩
        · rfl

end TasteGate

end BEDC.Derived.TwinSubstrateAuditPacketUp
