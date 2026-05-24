import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalDiameterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalDiameterUp : Type where
  | mk (I L U D R W H C P N : BHist) : DyadicIntervalDiameterUp
  deriving DecidableEq

def dyadicIntervalDiameterEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalDiameterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalDiameterEncodeBHist h

def dyadicIntervalDiameterDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalDiameterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalDiameterDecodeBHist tail)

private theorem dyadicIntervalDiameter_decode_encode :
    forall h : BHist,
      dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalDiameterFields : DyadicIntervalDiameterUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalDiameterUp.mk I L U D R W H C P N => [I, L, U, D, R, W, H, C, P, N]

def dyadicIntervalDiameterToEventFlow : DyadicIntervalDiameterUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalDiameterFields x).map dyadicIntervalDiameterEncodeBHist

def dyadicIntervalDiameterFromEventFlow :
    EventFlow -> Option DyadicIntervalDiameterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (DyadicIntervalDiameterUp.mk
                                                  (dyadicIntervalDiameterDecodeBHist I)
                                                  (dyadicIntervalDiameterDecodeBHist L)
                                                  (dyadicIntervalDiameterDecodeBHist U)
                                                  (dyadicIntervalDiameterDecodeBHist D)
                                                  (dyadicIntervalDiameterDecodeBHist R)
                                                  (dyadicIntervalDiameterDecodeBHist W)
                                                  (dyadicIntervalDiameterDecodeBHist H)
                                                  (dyadicIntervalDiameterDecodeBHist C)
                                                  (dyadicIntervalDiameterDecodeBHist P)
                                                  (dyadicIntervalDiameterDecodeBHist N))
                                          | _ :: _ => none

private theorem dyadicIntervalDiameter_round_trip :
    forall x : DyadicIntervalDiameterUp,
      dyadicIntervalDiameterFromEventFlow (dyadicIntervalDiameterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L U D R W H C P N =>
      change
        some
          (DyadicIntervalDiameterUp.mk
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist I))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist L))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist U))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist D))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist R))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist W))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist H))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist C))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist P))
            (dyadicIntervalDiameterDecodeBHist (dyadicIntervalDiameterEncodeBHist N))) =
          some (DyadicIntervalDiameterUp.mk I L U D R W H C P N)
      rw [dyadicIntervalDiameter_decode_encode I, dyadicIntervalDiameter_decode_encode L,
        dyadicIntervalDiameter_decode_encode U, dyadicIntervalDiameter_decode_encode D,
        dyadicIntervalDiameter_decode_encode R, dyadicIntervalDiameter_decode_encode W,
        dyadicIntervalDiameter_decode_encode H, dyadicIntervalDiameter_decode_encode C,
        dyadicIntervalDiameter_decode_encode P, dyadicIntervalDiameter_decode_encode N]

private theorem dyadicIntervalDiameterToEventFlow_injective {x y : DyadicIntervalDiameterUp} :
    dyadicIntervalDiameterToEventFlow x = dyadicIntervalDiameterToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalDiameterFromEventFlow (dyadicIntervalDiameterToEventFlow x) =
        dyadicIntervalDiameterFromEventFlow (dyadicIntervalDiameterToEventFlow y) :=
    congrArg dyadicIntervalDiameterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicIntervalDiameter_round_trip x).symm
      (Eq.trans hread (dyadicIntervalDiameter_round_trip y)))

private theorem dyadicIntervalDiameter_fields_faithful :
    forall x y : DyadicIntervalDiameterUp,
      dyadicIntervalDiameterFields x = dyadicIntervalDiameterFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 L1 U1 D1 R1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 L2 U2 D2 R2 W2 H2 C2 P2 N2 =>
          injection hfields with hI t1
          injection t1 with hL t2
          injection t2 with hU t3
          injection t3 with hD t4
          injection t4 with hR t5
          injection t5 with hW t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hI
          subst hL
          subst hU
          subst hD
          subst hR
          subst hW
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance dyadicIntervalDiameterBHistCarrier : BHistCarrier DyadicIntervalDiameterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalDiameterToEventFlow
  fromEventFlow := dyadicIntervalDiameterFromEventFlow

instance dyadicIntervalDiameterChapterTasteGate :
    ChapterTasteGate DyadicIntervalDiameterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalDiameterFromEventFlow (dyadicIntervalDiameterToEventFlow x) = some x
    exact dyadicIntervalDiameter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicIntervalDiameterToEventFlow_injective heq)

instance dyadicIntervalDiameterFieldFaithful : FieldFaithful DyadicIntervalDiameterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalDiameterFields
  field_faithful := dyadicIntervalDiameter_fields_faithful

def taste_gate : ChapterTasteGate DyadicIntervalDiameterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalDiameterChapterTasteGate

theorem DyadicIntervalDiameterTasteGate_single_carrier_alignment :
    (forall h : BHist, dyadicIntervalDiameterDecodeBHist
      (dyadicIntervalDiameterEncodeBHist h) = h) ∧
      (forall x : DyadicIntervalDiameterUp,
        dyadicIntervalDiameterFromEventFlow (dyadicIntervalDiameterToEventFlow x) = some x) ∧
        (forall x y : DyadicIntervalDiameterUp,
          dyadicIntervalDiameterToEventFlow x = dyadicIntervalDiameterToEventFlow y -> x = y) ∧
          dyadicIntervalDiameterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicIntervalDiameter_decode_encode
  · constructor
    · exact dyadicIntervalDiameter_round_trip
    · constructor
      · intro x y heq
        exact dyadicIntervalDiameterToEventFlow_injective heq
      · rfl

end BEDC.Derived.DyadicIntervalDiameterUp
