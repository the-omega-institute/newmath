import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSealCongruenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSealCongruenceUp : Type where
  | mk :
      (readback0 window0 seal0 readback1 window1 seal1 classifier replacement transport
        continuation provenance name : BHist) →
        RealSealCongruenceUp
  deriving DecidableEq

private def realSealCongruenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSealCongruenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSealCongruenceEncodeBHist h

private def realSealCongruenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSealCongruenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSealCongruenceDecodeBHist tail)

private theorem realSealCongruenceDecodeEncodeBHist :
    ∀ h : BHist,
      realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realSealCongruence_mk_congr
    {readback0 readback0' window0 window0' seal0 seal0' readback1 readback1' window1
      window1' seal1 seal1' classifier classifier' replacement replacement' transport
      transport' continuation continuation' provenance provenance' name name' : BHist}
    (hReadback0 : readback0' = readback0)
    (hWindow0 : window0' = window0)
    (hSeal0 : seal0' = seal0)
    (hReadback1 : readback1' = readback1)
    (hWindow1 : window1' = window1)
    (hSeal1 : seal1' = seal1)
    (hClassifier : classifier' = classifier)
    (hReplacement : replacement' = replacement)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RealSealCongruenceUp.mk readback0' window0' seal0' readback1' window1' seal1'
        classifier' replacement' transport' continuation' provenance' name' =
      RealSealCongruenceUp.mk readback0 window0 seal0 readback1 window1 seal1 classifier
        replacement transport continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hReadback0
  cases hWindow0
  cases hSeal0
  cases hReadback1
  cases hWindow1
  cases hSeal1
  cases hClassifier
  cases hReplacement
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

private def realSealCongruenceToEventFlow : RealSealCongruenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealSealCongruenceUp.mk readback0 window0 seal0 readback1 window1 seal1 classifier
      replacement transport continuation provenance name =>
      [[BMark.b0],
        realSealCongruenceEncodeBHist readback0,
        [BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist window0,
        [BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist seal0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist readback1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist window1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist seal1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realSealCongruenceEncodeBHist replacement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealCongruenceEncodeBHist name]

private def realSealCongruenceFromEventFlow :
    EventFlow → Option RealSealCongruenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | readback0 :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | window0 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | seal0 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readback1 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | window1 :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | seal1 :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | classifier :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replacement :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | continuation ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] =>
                                                                                          none
                                                                                      | provenance ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match rest22 with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | name ::
                                                                                                  rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (RealSealCongruenceUp.mk
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            readback0)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            window0)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            seal0)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            readback1)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            window1)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            seal1)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            classifier)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            replacement)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            transport)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            continuation)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            provenance)
                                                                                                          (realSealCongruenceDecodeBHist
                                                                                                            name))
                                                                                                  | _ :: _ =>
                                                                                                      none

private theorem realSealCongruenceRoundTrip :
    ∀ x : RealSealCongruenceUp,
      realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk readback0 window0 seal0 readback1 window1 seal1 classifier replacement transport
      continuation provenance name =>
      change
        some
          (RealSealCongruenceUp.mk
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist readback0))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist window0))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist seal0))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist readback1))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist window1))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist seal1))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist classifier))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist replacement))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist transport))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist continuation))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist provenance))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist name))) =
          some
            (RealSealCongruenceUp.mk readback0 window0 seal0 readback1 window1 seal1
              classifier replacement transport continuation provenance name)
      exact
        congrArg some
          (realSealCongruence_mk_congr
            (realSealCongruenceDecodeEncodeBHist readback0)
            (realSealCongruenceDecodeEncodeBHist window0)
            (realSealCongruenceDecodeEncodeBHist seal0)
            (realSealCongruenceDecodeEncodeBHist readback1)
            (realSealCongruenceDecodeEncodeBHist window1)
            (realSealCongruenceDecodeEncodeBHist seal1)
            (realSealCongruenceDecodeEncodeBHist classifier)
            (realSealCongruenceDecodeEncodeBHist replacement)
            (realSealCongruenceDecodeEncodeBHist transport)
            (realSealCongruenceDecodeEncodeBHist continuation)
            (realSealCongruenceDecodeEncodeBHist provenance)
            (realSealCongruenceDecodeEncodeBHist name))

private theorem realSealCongruenceToEventFlow_injective
    {x y : RealSealCongruenceUp} :
    realSealCongruenceToEventFlow x = realSealCongruenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) =
        realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow y) :=
    congrArg realSealCongruenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realSealCongruenceRoundTrip x).symm
      (Eq.trans hread (realSealCongruenceRoundTrip y)))

private def realSealCongruenceFields : RealSealCongruenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSealCongruenceUp.mk readback0 window0 seal0 readback1 window1 seal1 classifier
      replacement transport continuation provenance name =>
      [readback0, window0, seal0, readback1, window1, seal1, classifier, replacement,
        transport, continuation, provenance, name]

private theorem realSealCongruence_field_faithful :
    ∀ x y : RealSealCongruenceUp,
      realSealCongruenceFields x = realSealCongruenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk readback0 window0 seal0 readback1 window1 seal1 classifier replacement transport
      continuation provenance name =>
      cases y with
      | mk readback0' window0' seal0' readback1' window1' seal1' classifier'
          replacement' transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance realSealCongruenceBHistCarrier : BHistCarrier RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSealCongruenceToEventFlow
  fromEventFlow := realSealCongruenceFromEventFlow

instance realSealCongruenceChapterTasteGate :
    ChapterTasteGate RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) = some x
    exact realSealCongruenceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSealCongruenceToEventFlow_injective heq)

instance realSealCongruenceFieldFaithful : FieldFaithful RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSealCongruenceFields
  field_faithful := realSealCongruence_field_faithful

instance realSealCongruenceNontrivial : Nontrivial RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSealCongruenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealSealCongruenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealSealCongruenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSealCongruenceChapterTasteGate

theorem RealSealCongruenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, realSealCongruenceDecodeBHist
        (realSealCongruenceEncodeBHist h) = h) ∧
      (∀ x : RealSealCongruenceUp,
        realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) = some x) ∧
        (∀ x y : RealSealCongruenceUp,
          realSealCongruenceToEventFlow x = realSealCongruenceToEventFlow y → x = y) ∧
          realSealCongruenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realSealCongruenceDecodeEncodeBHist
  · constructor
    · exact realSealCongruenceRoundTrip
    · constructor
      · intro x y heq
        exact realSealCongruenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealSealCongruenceUp
