import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistArity13TupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistArity13TupleNameCertUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L : BHist) :
      BHistArity13TupleNameCertUp
  deriving DecidableEq

def bHistArity13TupleNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistArity13TupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistArity13TupleNameCertEncodeBHist h

def bHistArity13TupleNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistArity13TupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistArity13TupleNameCertDecodeBHist tail)

private theorem BHistArity13TupleNameCertCarrierAdmission_decode :
    forall h : BHist, bHistArity13TupleNameCertDecodeBHist
      (bHistArity13TupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistArity13TupleNameCertFields : BHistArity13TupleNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity13TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, H, C, P, L]

def bHistArity13TupleNameCertToEventFlow : BHistArity13TupleNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity13TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L =>
      [[BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R0,
        [BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R2,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R3,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R4,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R5,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R6,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R7,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R8,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R9,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R10,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R11,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist R12,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistArity13TupleNameCertEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistArity13TupleNameCertEncodeBHist L]

private def bHistArity13TupleNameCertDecodePacket
    (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L : RawEvent) :
    BHistArity13TupleNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistArity13TupleNameCertUp.mk
    (bHistArity13TupleNameCertDecodeBHist R0)
    (bHistArity13TupleNameCertDecodeBHist R1)
    (bHistArity13TupleNameCertDecodeBHist R2)
    (bHistArity13TupleNameCertDecodeBHist R3)
    (bHistArity13TupleNameCertDecodeBHist R4)
    (bHistArity13TupleNameCertDecodeBHist R5)
    (bHistArity13TupleNameCertDecodeBHist R6)
    (bHistArity13TupleNameCertDecodeBHist R7)
    (bHistArity13TupleNameCertDecodeBHist R8)
    (bHistArity13TupleNameCertDecodeBHist R9)
    (bHistArity13TupleNameCertDecodeBHist R10)
    (bHistArity13TupleNameCertDecodeBHist R11)
    (bHistArity13TupleNameCertDecodeBHist R12)
    (bHistArity13TupleNameCertDecodeBHist H)
    (bHistArity13TupleNameCertDecodeBHist C)
    (bHistArity13TupleNameCertDecodeBHist P)
    (bHistArity13TupleNameCertDecodeBHist L)

def bHistArity13TupleNameCertFromEventFlow : EventFlow -> Option BHistArity13TupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | R0 :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | R1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R2 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R3 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R4 :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R5 :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | R6 :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | R7 :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | R8 :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | R9 :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | R10 :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | R11 :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | R12 :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] => none
                                                                                                          | _tag13 :: rest26 =>
                                                                                                              match rest26 with
                                                                                                              | [] => none
                                                                                                              | H :: rest27 =>
                                                                                                                  match rest27 with
                                                                                                                  | [] => none
                                                                                                                  | _tag14 :: rest28 =>
                                                                                                                      match rest28 with
                                                                                                                      | [] => none
                                                                                                                      | C :: rest29 =>
                                                                                                                          match rest29 with
                                                                                                                          | [] => none
                                                                                                                          | _tag15 :: rest30 =>
                                                                                                                              match rest30 with
                                                                                                                              | [] => none
                                                                                                                              | P :: rest31 =>
                                                                                                                                  match rest31 with
                                                                                                                                  | [] => none
                                                                                                                                  | _tag16 :: rest32 =>
                                                                                                                                      match rest32 with
                                                                                                                                      | [] => none
                                                                                                                                      | L :: rest33 =>
                                                                                                                                          match rest33 with
                                                                                                                                          | [] =>
                                                                                                                                              some
                                                                                                                                                (bHistArity13TupleNameCertDecodePacket R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L)
                                                                                                                                          | _ :: _ => none

private theorem BHistArity13TupleNameCertCarrierAdmission_round_trip :
    forall x : BHistArity13TupleNameCertUp,
      bHistArity13TupleNameCertFromEventFlow
        (bHistArity13TupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L =>
      change
        some
          (bHistArity13TupleNameCertDecodePacket
            (bHistArity13TupleNameCertEncodeBHist R0)
            (bHistArity13TupleNameCertEncodeBHist R1)
            (bHistArity13TupleNameCertEncodeBHist R2)
            (bHistArity13TupleNameCertEncodeBHist R3)
            (bHistArity13TupleNameCertEncodeBHist R4)
            (bHistArity13TupleNameCertEncodeBHist R5)
            (bHistArity13TupleNameCertEncodeBHist R6)
            (bHistArity13TupleNameCertEncodeBHist R7)
            (bHistArity13TupleNameCertEncodeBHist R8)
            (bHistArity13TupleNameCertEncodeBHist R9)
            (bHistArity13TupleNameCertEncodeBHist R10)
            (bHistArity13TupleNameCertEncodeBHist R11)
            (bHistArity13TupleNameCertEncodeBHist R12)
            (bHistArity13TupleNameCertEncodeBHist H)
            (bHistArity13TupleNameCertEncodeBHist C)
            (bHistArity13TupleNameCertEncodeBHist P)
            (bHistArity13TupleNameCertEncodeBHist L)) =
          some
            (BHistArity13TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9
              R10 R11 R12 H C P L)
      unfold bHistArity13TupleNameCertDecodePacket
      rw [BHistArity13TupleNameCertCarrierAdmission_decode R0,
        BHistArity13TupleNameCertCarrierAdmission_decode R1,
        BHistArity13TupleNameCertCarrierAdmission_decode R2,
        BHistArity13TupleNameCertCarrierAdmission_decode R3,
        BHistArity13TupleNameCertCarrierAdmission_decode R4,
        BHistArity13TupleNameCertCarrierAdmission_decode R5,
        BHistArity13TupleNameCertCarrierAdmission_decode R6,
        BHistArity13TupleNameCertCarrierAdmission_decode R7,
        BHistArity13TupleNameCertCarrierAdmission_decode R8,
        BHistArity13TupleNameCertCarrierAdmission_decode R9,
        BHistArity13TupleNameCertCarrierAdmission_decode R10,
        BHistArity13TupleNameCertCarrierAdmission_decode R11,
        BHistArity13TupleNameCertCarrierAdmission_decode R12,
        BHistArity13TupleNameCertCarrierAdmission_decode H,
        BHistArity13TupleNameCertCarrierAdmission_decode C,
        BHistArity13TupleNameCertCarrierAdmission_decode P,
        BHistArity13TupleNameCertCarrierAdmission_decode L]

private theorem BHistArity13TupleNameCertCarrierAdmission_injective
    {x y : BHistArity13TupleNameCertUp} :
    bHistArity13TupleNameCertToEventFlow x =
        bHistArity13TupleNameCertToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistArity13TupleNameCertFromEventFlow
          (bHistArity13TupleNameCertToEventFlow x) =
        bHistArity13TupleNameCertFromEventFlow
          (bHistArity13TupleNameCertToEventFlow y) :=
    congrArg bHistArity13TupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistArity13TupleNameCertCarrierAdmission_round_trip x).symm
      (Eq.trans hread (BHistArity13TupleNameCertCarrierAdmission_round_trip y)))

private theorem BHistArity13TupleNameCertCarrierAdmission_field_faithful :
    forall x y : BHistArity13TupleNameCertUp,
      bHistArity13TupleNameCertFields x = bHistArity13TupleNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 R101 R111 R121 H1 C1 P1 L1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 R102 R112 R122 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance bHistArity13TupleNameCertBHistCarrier :
    BHistCarrier BHistArity13TupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistArity13TupleNameCertToEventFlow
  fromEventFlow := bHistArity13TupleNameCertFromEventFlow

instance bHistArity13TupleNameCertChapterTasteGate :
    ChapterTasteGate BHistArity13TupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistArity13TupleNameCertFromEventFlow
          (bHistArity13TupleNameCertToEventFlow x) = some x
    exact BHistArity13TupleNameCertCarrierAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistArity13TupleNameCertCarrierAdmission_injective heq)

instance bHistArity13TupleNameCertFieldFaithful :
    FieldFaithful BHistArity13TupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistArity13TupleNameCertFields
  field_faithful := BHistArity13TupleNameCertCarrierAdmission_field_faithful

theorem BHistArity13TupleNameCertCarrierAdmission :
    (forall x : BHistArity13TupleNameCertUp,
      bHistArity13TupleNameCertFromEventFlow
          (bHistArity13TupleNameCertToEventFlow x) = some x) /\
    (forall R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L : BHist,
      bHistArity13TupleNameCertFields
          (BHistArity13TupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
            R11 R12 H C P L) =
        [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, H, C, P,
          L]) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BHistArity13TupleNameCertCarrierAdmission_round_trip
  · intro R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 H C P L
    rfl

end BEDC.Derived.BHistArity13TupleNameCertUp
