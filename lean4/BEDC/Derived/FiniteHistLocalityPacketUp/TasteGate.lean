import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteHistLocalityPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteHistLocalityPacketUp : Type where
  | mk :
      (historyLeft historyRight locality invariant symmetry transport replay provenance
        localName : BHist) →
      FiniteHistLocalityPacketUp
  deriving DecidableEq

def finiteHistLocalityPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteHistLocalityPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteHistLocalityPacketEncodeBHist h

def finiteHistLocalityPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteHistLocalityPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteHistLocalityPacketDecodeBHist tail)

private theorem finiteHistLocalityPacket_decode_encode_bhist :
    ∀ h : BHist,
      finiteHistLocalityPacketDecodeBHist
        (finiteHistLocalityPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteHistLocalityPacketToEventFlow : FiniteHistLocalityPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteHistLocalityPacketUp.mk historyLeft historyRight locality invariant symmetry transport
      replay provenance localName =>
      [[BMark.b0],
        finiteHistLocalityPacketEncodeBHist historyLeft,
        [BMark.b1, BMark.b0],
        finiteHistLocalityPacketEncodeBHist historyRight,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteHistLocalityPacketEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHistLocalityPacketEncodeBHist invariant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHistLocalityPacketEncodeBHist symmetry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHistLocalityPacketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteHistLocalityPacketEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteHistLocalityPacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteHistLocalityPacketEncodeBHist localName]

def finiteHistLocalityPacketFromEventFlow : EventFlow → Option FiniteHistLocalityPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | historyLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | historyRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | locality :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | invariant :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | symmetry :: rest9 =>
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
                                                      | replay :: rest13 =>
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
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (FiniteHistLocalityPacketUp.mk
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    historyLeft)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    historyRight)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    locality)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    invariant)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    symmetry)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    transport)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    replay)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    provenance)
                                                                                  (finiteHistLocalityPacketDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ =>
                                                                              none

private theorem finiteHistLocalityPacket_round_trip :
    ∀ x : FiniteHistLocalityPacketUp,
      finiteHistLocalityPacketFromEventFlow
        (finiteHistLocalityPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk historyLeft historyRight locality invariant symmetry transport replay provenance
      localName =>
      change
        some
          (FiniteHistLocalityPacketUp.mk
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist historyLeft))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist historyRight))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist locality))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist invariant))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist symmetry))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist transport))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist replay))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist provenance))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist localName))) =
          some
            (FiniteHistLocalityPacketUp.mk historyLeft historyRight locality invariant symmetry
              transport replay provenance localName)
      rw [finiteHistLocalityPacket_decode_encode_bhist historyLeft,
        finiteHistLocalityPacket_decode_encode_bhist historyRight,
        finiteHistLocalityPacket_decode_encode_bhist locality,
        finiteHistLocalityPacket_decode_encode_bhist invariant,
        finiteHistLocalityPacket_decode_encode_bhist symmetry,
        finiteHistLocalityPacket_decode_encode_bhist transport,
        finiteHistLocalityPacket_decode_encode_bhist replay,
        finiteHistLocalityPacket_decode_encode_bhist provenance,
        finiteHistLocalityPacket_decode_encode_bhist localName]

private theorem finiteHistLocalityPacketToEventFlow_injective
    {x y : FiniteHistLocalityPacketUp} :
    finiteHistLocalityPacketToEventFlow x =
      finiteHistLocalityPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow y) :=
    congrArg finiteHistLocalityPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteHistLocalityPacket_round_trip x).symm
      (Eq.trans hread (finiteHistLocalityPacket_round_trip y)))

instance finiteHistLocalityPacketBHistCarrier :
    BHistCarrier FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteHistLocalityPacketToEventFlow
  fromEventFlow := finiteHistLocalityPacketFromEventFlow

instance finiteHistLocalityPacketChapterTasteGate :
    ChapterTasteGate FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        some x
    exact finiteHistLocalityPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteHistLocalityPacketToEventFlow_injective heq)

instance finiteHistLocalityPacketFieldFaithful :
    FieldFaithful FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | FiniteHistLocalityPacketUp.mk historyLeft historyRight locality invariant symmetry
        transport replay provenance localName =>
        [historyLeft, historyRight, locality, invariant, symmetry, transport, replay,
          provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk historyLeft historyRight locality invariant symmetry transport replay provenance
        localName =>
        cases y with
        | mk historyLeft' historyRight' locality' invariant' symmetry' transport' replay'
            provenance' localName' =>
            injection hfields with hHistoryLeft hTail0
            injection hTail0 with hHistoryRight hTail1
            injection hTail1 with hLocality hTail2
            injection hTail2 with hInvariant hTail3
            injection hTail3 with hSymmetry hTail4
            injection hTail4 with hTransport hTail5
            injection hTail5 with hReplay hTail6
            injection hTail6 with hProvenance hTail7
            injection hTail7 with hLocalName _hNil
            cases hHistoryLeft
            cases hHistoryRight
            cases hLocality
            cases hInvariant
            cases hSymmetry
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

instance finiteHistLocalityPacketNontrivial :
    Nontrivial FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteHistLocalityPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteHistLocalityPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteHistLocalityPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteHistLocalityPacketChapterTasteGate

end BEDC.Derived.FiniteHistLocalityPacketUp
