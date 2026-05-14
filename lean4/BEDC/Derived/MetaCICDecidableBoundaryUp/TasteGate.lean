import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDecidableBoundaryUp : Type where
  | mk :
      (checker structural boundedNormal finished refusal transport replay provenance
        localName : BHist) →
      MetaCICDecidableBoundaryUp
  deriving DecidableEq

def metaCICDecidableBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICDecidableBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICDecidableBoundaryEncodeBHist h

def metaCICDecidableBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICDecidableBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICDecidableBoundaryDecodeBHist tail)

private theorem metaCICDecidableBoundary_decode_encode_bhist :
    ∀ h : BHist,
      metaCICDecidableBoundaryDecodeBHist
        (metaCICDecidableBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICDecidableBoundaryToEventFlow :
    MetaCICDecidableBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDecidableBoundaryUp.mk checker structural boundedNormal finished refusal transport
      replay provenance localName =>
      [[BMark.b0],
        metaCICDecidableBoundaryEncodeBHist checker,
        [BMark.b1, BMark.b0],
        metaCICDecidableBoundaryEncodeBHist structural,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICDecidableBoundaryEncodeBHist boundedNormal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDecidableBoundaryEncodeBHist finished,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDecidableBoundaryEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDecidableBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDecidableBoundaryEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICDecidableBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICDecidableBoundaryEncodeBHist localName]

def metaCICDecidableBoundaryFromEventFlow :
    EventFlow → Option MetaCICDecidableBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | checker :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | structural :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | boundedNormal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | finished :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
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
                                                              | provenance ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] =>
                                                                          none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (MetaCICDecidableBoundaryUp.mk
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    checker)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    structural)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    boundedNormal)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    finished)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    refusal)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    transport)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    replay)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    provenance)
                                                                                  (metaCICDecidableBoundaryDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ =>
                                                                              none

private theorem metaCICDecidableBoundary_round_trip :
    ∀ x : MetaCICDecidableBoundaryUp,
      metaCICDecidableBoundaryFromEventFlow
        (metaCICDecidableBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk checker structural boundedNormal finished refusal transport replay provenance localName =>
      change
        some
          (MetaCICDecidableBoundaryUp.mk
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist checker))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist structural))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist boundedNormal))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist finished))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist refusal))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist transport))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist replay))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist provenance))
            (metaCICDecidableBoundaryDecodeBHist
              (metaCICDecidableBoundaryEncodeBHist localName))) =
          some
            (MetaCICDecidableBoundaryUp.mk checker structural boundedNormal finished refusal
              transport replay provenance localName)
      rw [metaCICDecidableBoundary_decode_encode_bhist checker,
        metaCICDecidableBoundary_decode_encode_bhist structural,
        metaCICDecidableBoundary_decode_encode_bhist boundedNormal,
        metaCICDecidableBoundary_decode_encode_bhist finished,
        metaCICDecidableBoundary_decode_encode_bhist refusal,
        metaCICDecidableBoundary_decode_encode_bhist transport,
        metaCICDecidableBoundary_decode_encode_bhist replay,
        metaCICDecidableBoundary_decode_encode_bhist provenance,
        metaCICDecidableBoundary_decode_encode_bhist localName]

private theorem metaCICDecidableBoundaryToEventFlow_injective
    {x y : MetaCICDecidableBoundaryUp} :
    metaCICDecidableBoundaryToEventFlow x =
      metaCICDecidableBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICDecidableBoundaryFromEventFlow
          (metaCICDecidableBoundaryToEventFlow x) =
        metaCICDecidableBoundaryFromEventFlow
          (metaCICDecidableBoundaryToEventFlow y) :=
    congrArg metaCICDecidableBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICDecidableBoundary_round_trip x).symm
      (Eq.trans hread (metaCICDecidableBoundary_round_trip y)))

instance metaCICDecidableBoundaryBHistCarrier :
    BHistCarrier MetaCICDecidableBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICDecidableBoundaryToEventFlow
  fromEventFlow := metaCICDecidableBoundaryFromEventFlow

instance metaCICDecidableBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICDecidableBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICDecidableBoundaryFromEventFlow
        (metaCICDecidableBoundaryToEventFlow x) = some x
    exact metaCICDecidableBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICDecidableBoundaryToEventFlow_injective heq)

instance metaCICDecidableBoundaryFieldFaithful :
    FieldFaithful MetaCICDecidableBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | MetaCICDecidableBoundaryUp.mk checker structural boundedNormal finished refusal transport
        replay provenance localName =>
        [checker, structural, boundedNormal, finished, refusal, transport, replay, provenance,
          localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk checker structural boundedNormal finished refusal transport replay provenance localName =>
        cases y with
        | mk checker' structural' boundedNormal' finished' refusal' transport' replay'
            provenance' localName' =>
            injection hfields with hChecker hTail0
            injection hTail0 with hStructural hTail1
            injection hTail1 with hBoundedNormal hTail2
            injection hTail2 with hFinished hTail3
            injection hTail3 with hRefusal hTail4
            injection hTail4 with hTransport hTail5
            injection hTail5 with hReplay hTail6
            injection hTail6 with hProvenance hTail7
            injection hTail7 with hLocalName _hNil
            cases hChecker
            cases hStructural
            cases hBoundedNormal
            cases hFinished
            cases hRefusal
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

theorem MetaCICDecidableBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICDecidableBoundaryDecodeBHist
        (metaCICDecidableBoundaryEncodeBHist h) = h) ∧
      (∀ x : MetaCICDecidableBoundaryUp,
        metaCICDecidableBoundaryFromEventFlow
          (metaCICDecidableBoundaryToEventFlow x) = some x) ∧
        (∀ x y : MetaCICDecidableBoundaryUp,
          metaCICDecidableBoundaryToEventFlow x =
            metaCICDecidableBoundaryToEventFlow y → x = y) ∧
          metaCICDecidableBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICDecidableBoundary_decode_encode_bhist
  · constructor
    · exact metaCICDecidableBoundary_round_trip
    · constructor
      · intro x y heq
        exact metaCICDecidableBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICDecidableBoundaryUp
