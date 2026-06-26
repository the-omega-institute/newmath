import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyBornologyBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyBornologyBasisUp : Type where
  | mk (F G M S W D R E H C P N : BHist) : CauchyBornologyBasisUp
  deriving DecidableEq

def cauchyBornologyBasisEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyBornologyBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyBornologyBasisEncodeBHist h

def cauchyBornologyBasisDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyBornologyBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyBornologyBasisDecodeBHist tail)

private theorem CauchyBornologyBasisTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyBornologyBasisFields : CauchyBornologyBasisUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyBornologyBasisUp.mk F G M S W D R E H C P N =>
      [F, G, M, S, W, D, R, E, H, C, P, N]

def cauchyBornologyBasisToEventFlow : CauchyBornologyBasisUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyBornologyBasisFields x).map cauchyBornologyBasisEncodeBHist

def cauchyBornologyBasisFromEventFlow : EventFlow -> Option CauchyBornologyBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | G :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (CauchyBornologyBasisUp.mk
                                                          (cauchyBornologyBasisDecodeBHist F)
                                                          (cauchyBornologyBasisDecodeBHist G)
                                                          (cauchyBornologyBasisDecodeBHist M)
                                                          (cauchyBornologyBasisDecodeBHist S)
                                                          (cauchyBornologyBasisDecodeBHist W)
                                                          (cauchyBornologyBasisDecodeBHist D)
                                                          (cauchyBornologyBasisDecodeBHist R)
                                                          (cauchyBornologyBasisDecodeBHist E)
                                                          (cauchyBornologyBasisDecodeBHist H)
                                                          (cauchyBornologyBasisDecodeBHist C)
                                                          (cauchyBornologyBasisDecodeBHist P)
                                                          (cauchyBornologyBasisDecodeBHist N))
                                                  | _ :: _ => none

private theorem CauchyBornologyBasisTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyBornologyBasisUp,
      cauchyBornologyBasisFromEventFlow (cauchyBornologyBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G M S W D R E H C P N =>
      change
        some
          (CauchyBornologyBasisUp.mk
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist F))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist G))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist M))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist S))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist W))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist D))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist R))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist E))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist H))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist C))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist P))
            (cauchyBornologyBasisDecodeBHist (cauchyBornologyBasisEncodeBHist N))) =
          some (CauchyBornologyBasisUp.mk F G M S W D R E H C P N)
      rw [CauchyBornologyBasisTasteGate_single_carrier_alignment_decode F,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode G,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode M,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode S,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode W,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode D,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode R,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode E,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode H,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode C,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode P,
        CauchyBornologyBasisTasteGate_single_carrier_alignment_decode N]

private theorem CauchyBornologyBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyBornologyBasisUp} :
    cauchyBornologyBasisToEventFlow x = cauchyBornologyBasisToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyBornologyBasisFromEventFlow (cauchyBornologyBasisToEventFlow x) =
        cauchyBornologyBasisFromEventFlow (cauchyBornologyBasisToEventFlow y) :=
    congrArg cauchyBornologyBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyBornologyBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyBornologyBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyBornologyBasisTasteGate_single_carrier_alignment_fields :
    forall x y : CauchyBornologyBasisUp,
      cauchyBornologyBasisFields x = cauchyBornologyBasisFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 G1 M1 S1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 G2 M2 S2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyBornologyBasisBHistCarrier : BHistCarrier CauchyBornologyBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyBornologyBasisToEventFlow
  fromEventFlow := cauchyBornologyBasisFromEventFlow

instance cauchyBornologyBasisChapterTasteGate : ChapterTasteGate CauchyBornologyBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyBornologyBasisFromEventFlow (cauchyBornologyBasisToEventFlow x) = some x
    exact CauchyBornologyBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyBornologyBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyBornologyBasisFieldFaithful : FieldFaithful CauchyBornologyBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyBornologyBasisFields
  field_faithful := CauchyBornologyBasisTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate CauchyBornologyBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyBornologyBasisChapterTasteGate

namespace TasteGate

theorem CauchyBornologyBasisTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyBornologyBasisDecodeBHist
      (cauchyBornologyBasisEncodeBHist h) = h) /\
      (forall x : CauchyBornologyBasisUp,
        cauchyBornologyBasisFromEventFlow (cauchyBornologyBasisToEventFlow x) = some x) /\
        (forall x y : CauchyBornologyBasisUp,
          cauchyBornologyBasisToEventFlow x = cauchyBornologyBasisToEventFlow y -> x = y) /\
          cauchyBornologyBasisEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyBornologyBasisTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CauchyBornologyBasisTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyBornologyBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.CauchyBornologyBasisUp
