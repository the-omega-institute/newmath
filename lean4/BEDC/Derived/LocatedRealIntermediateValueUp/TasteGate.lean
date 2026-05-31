import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealIntermediateValueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealIntermediateValueUp : Type where
  | mk (I S B Q W R E H C P N : BHist) : LocatedRealIntermediateValueUp
  deriving DecidableEq

def locatedRealIntermediateValueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealIntermediateValueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealIntermediateValueEncodeBHist h

def locatedRealIntermediateValueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealIntermediateValueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealIntermediateValueDecodeBHist tail)

private theorem LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealIntermediateValueDecodeBHist
        (locatedRealIntermediateValueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealIntermediateValueToEventFlow : LocatedRealIntermediateValueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealIntermediateValueUp.mk I S B Q W R E H C P N =>
      [locatedRealIntermediateValueEncodeBHist I,
        locatedRealIntermediateValueEncodeBHist S,
        locatedRealIntermediateValueEncodeBHist B,
        locatedRealIntermediateValueEncodeBHist Q,
        locatedRealIntermediateValueEncodeBHist W,
        locatedRealIntermediateValueEncodeBHist R,
        locatedRealIntermediateValueEncodeBHist E,
        locatedRealIntermediateValueEncodeBHist H,
        locatedRealIntermediateValueEncodeBHist C,
        locatedRealIntermediateValueEncodeBHist P,
        locatedRealIntermediateValueEncodeBHist N]

def locatedRealIntermediateValueFromEventFlow :
    EventFlow → Option LocatedRealIntermediateValueUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (LocatedRealIntermediateValueUp.mk
                                                      (locatedRealIntermediateValueDecodeBHist I)
                                                      (locatedRealIntermediateValueDecodeBHist S)
                                                      (locatedRealIntermediateValueDecodeBHist B)
                                                      (locatedRealIntermediateValueDecodeBHist Q)
                                                      (locatedRealIntermediateValueDecodeBHist W)
                                                      (locatedRealIntermediateValueDecodeBHist R)
                                                      (locatedRealIntermediateValueDecodeBHist E)
                                                      (locatedRealIntermediateValueDecodeBHist H)
                                                      (locatedRealIntermediateValueDecodeBHist C)
                                                      (locatedRealIntermediateValueDecodeBHist P)
                                                      (locatedRealIntermediateValueDecodeBHist N))
                                              | _ :: _ => none

theorem LocatedRealIntermediateValueTasteGate_single_carrier_alignment :
    ∀ x : LocatedRealIntermediateValueUp,
      locatedRealIntermediateValueFromEventFlow
          (locatedRealIntermediateValueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S B Q W R E H C P N =>
      change
        some
          (LocatedRealIntermediateValueUp.mk
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist I))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist S))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist B))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist Q))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist W))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist R))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist E))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist H))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist C))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist P))
            (locatedRealIntermediateValueDecodeBHist
              (locatedRealIntermediateValueEncodeBHist N))) =
          some (LocatedRealIntermediateValueUp.mk I S B Q W R E H C P N)
      rw [LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode I,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode S,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode B,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode Q,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode W,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode R,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode E,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode H,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode C,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode P,
        LocatedRealIntermediateValueTasteGate_single_carrier_alignment_decode N]

private theorem locatedRealIntermediateValueToEventFlow_injective
    {x y : LocatedRealIntermediateValueUp} :
    locatedRealIntermediateValueToEventFlow x =
        locatedRealIntermediateValueToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealIntermediateValueFromEventFlow
          (locatedRealIntermediateValueToEventFlow x) =
        locatedRealIntermediateValueFromEventFlow
          (locatedRealIntermediateValueToEventFlow y) :=
    congrArg locatedRealIntermediateValueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealIntermediateValueTasteGate_single_carrier_alignment x).symm
      (Eq.trans hread
        (LocatedRealIntermediateValueTasteGate_single_carrier_alignment y)))

instance locatedRealIntermediateValueBHistCarrier :
    BHistCarrier LocatedRealIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealIntermediateValueToEventFlow
  fromEventFlow := locatedRealIntermediateValueFromEventFlow

instance locatedRealIntermediateValueChapterTasteGate :
    ChapterTasteGate LocatedRealIntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealIntermediateValueFromEventFlow
        (locatedRealIntermediateValueToEventFlow x) = some x
    exact LocatedRealIntermediateValueTasteGate_single_carrier_alignment x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealIntermediateValueToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealIntermediateValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealIntermediateValueChapterTasteGate

end BEDC.Derived.LocatedRealIntermediateValueUp
