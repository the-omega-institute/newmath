import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PeanoExistenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PeanoExistenceUp : Type where
  | mk
      (intervalSource vectorField closedWindow eulerLedger compactContainment modulus
        transport continuation provenance name : BHist) :
      PeanoExistenceUp
  deriving DecidableEq

def peanoExistenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: peanoExistenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: peanoExistenceEncodeBHist h

def peanoExistenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (peanoExistenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (peanoExistenceDecodeBHist tail)

private theorem PeanoExistenceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, peanoExistenceDecodeBHist (peanoExistenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def peanoExistenceToEventFlow : PeanoExistenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PeanoExistenceUp.mk intervalSource vectorField closedWindow eulerLedger compactContainment
      modulus transport continuation provenance name =>
      [[BMark.b0],
        peanoExistenceEncodeBHist intervalSource,
        [BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist vectorField,
        [BMark.b1, BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist closedWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist eulerLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist compactContainment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        peanoExistenceEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        peanoExistenceEncodeBHist name]

def peanoExistenceFromEventFlow : EventFlow -> Option PeanoExistenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | intervalSource :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | vectorField :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | closedWindow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | eulerLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | compactContainment :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | modulus :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (PeanoExistenceUp.mk
                                                                                          (peanoExistenceDecodeBHist
                                                                                            intervalSource)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            vectorField)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            closedWindow)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            eulerLedger)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            compactContainment)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            modulus)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            transport)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            continuation)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            provenance)
                                                                                          (peanoExistenceDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem PeanoExistenceTasteGate_single_carrier_alignment_round_trip :
    forall x : PeanoExistenceUp,
      peanoExistenceFromEventFlow (peanoExistenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk intervalSource vectorField closedWindow eulerLedger compactContainment modulus
      transport continuation provenance name =>
      change
        some
          (PeanoExistenceUp.mk
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist intervalSource))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist vectorField))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist closedWindow))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist eulerLedger))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist compactContainment))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist modulus))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist transport))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist continuation))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist provenance))
            (peanoExistenceDecodeBHist (peanoExistenceEncodeBHist name))) =
          some
            (PeanoExistenceUp.mk intervalSource vectorField closedWindow eulerLedger
              compactContainment modulus transport continuation provenance name)
      rw [PeanoExistenceTasteGate_single_carrier_alignment_decode_encode intervalSource,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode vectorField,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode closedWindow,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode eulerLedger,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode compactContainment,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode modulus,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode transport,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode continuation,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode provenance,
        PeanoExistenceTasteGate_single_carrier_alignment_decode_encode name]

private theorem PeanoExistenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PeanoExistenceUp} :
    peanoExistenceToEventFlow x = peanoExistenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      peanoExistenceFromEventFlow (peanoExistenceToEventFlow x) =
        peanoExistenceFromEventFlow (peanoExistenceToEventFlow y) :=
    congrArg peanoExistenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PeanoExistenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PeanoExistenceTasteGate_single_carrier_alignment_round_trip y)))

instance peanoExistenceBHistCarrier : BHistCarrier PeanoExistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := peanoExistenceToEventFlow
  fromEventFlow := peanoExistenceFromEventFlow

instance peanoExistenceChapterTasteGate : ChapterTasteGate PeanoExistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change peanoExistenceFromEventFlow (peanoExistenceToEventFlow x) = some x
    exact PeanoExistenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PeanoExistenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PeanoExistenceTasteGate_single_carrier_alignment :
    (forall h : BHist, peanoExistenceDecodeBHist (peanoExistenceEncodeBHist h) = h) /\
      (forall x : PeanoExistenceUp,
        peanoExistenceFromEventFlow (peanoExistenceToEventFlow x) = some x) /\
        (forall x y : PeanoExistenceUp,
          peanoExistenceToEventFlow x = peanoExistenceToEventFlow y -> x = y) /\
          (forall x y : PeanoExistenceUp,
            x ≠ y -> peanoExistenceToEventFlow x ≠ peanoExistenceToEventFlow y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PeanoExistenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact PeanoExistenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact PeanoExistenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · intro x y hxy heq
        exact hxy (PeanoExistenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

end BEDC.Derived.PeanoExistenceUp.TasteGate
