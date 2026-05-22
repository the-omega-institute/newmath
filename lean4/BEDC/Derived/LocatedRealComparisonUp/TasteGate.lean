import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealComparisonUp : Type where
  | mk : (L0 L1 W R0 R1 D0 D1 B A H C P N : BHist) -> LocatedRealComparisonUp
  deriving DecidableEq

def LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist h

def LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
        (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def LocatedRealComparisonTasteGate_single_carrier_alignment_fields :
    LocatedRealComparisonUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealComparisonUp.mk L0 L1 W R0 R1 D0 D1 B A H C P N =>
      [L0, L1, W, R0, R1, D0, D1, B, A, H, C, P, N]

def LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow :
    LocatedRealComparisonUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (LocatedRealComparisonTasteGate_single_carrier_alignment_fields x).map
        LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist

def LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option LocatedRealComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L0 :: rest0 =>
      match rest0 with
      | [] => none
      | L1 :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R0 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R1 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D0 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D1 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | B :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | A :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (LocatedRealComparisonUp.mk
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist L0)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist L1)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist W)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist R0)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist R1)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist D0)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist D1)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist B)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist A)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist H)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist C)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist P)
                                                              (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist N))
                                                      | _ :: _ => none

private theorem LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip :
    forall x : LocatedRealComparisonUp,
      LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow
        (LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L0 L1 W R0 R1 D0 D1 B A H C P N =>
      change
        some
          (LocatedRealComparisonUp.mk
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist L0))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist L1))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist W))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist R0))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist R1))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist D0))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist D1))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist B))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist A))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist H))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist C))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist P))
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decodeBHist
              (LocatedRealComparisonTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (LocatedRealComparisonUp.mk L0 L1 W R0 R1 D0 D1 B A H C P N)
      rw [LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode L0,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode L1,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode W,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode R0,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode R1,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode D0,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode D1,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode B,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode A,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode H,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode C,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode P,
        LocatedRealComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealComparisonUp} :
    LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow x =
      LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread : some x = some y := by
    calc
      some x =
          LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow
            (LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow x) :=
        (LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow
            (LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y :=
        LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hread

private theorem LocatedRealComparisonTasteGate_single_carrier_alignment_field_faithful :
    forall x y : LocatedRealComparisonUp,
      LocatedRealComparisonTasteGate_single_carrier_alignment_fields x =
        LocatedRealComparisonTasteGate_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L01 L11 W1 R01 R11 D01 D11 B1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk L02 L12 W2 R02 R12 D02 D12 B2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedRealComparisonBHistCarrier : BHistCarrier LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow

instance locatedRealComparisonChapterTasteGate :
    ChapterTasteGate LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow
        (LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedRealComparisonFieldFaithful : FieldFaithful LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := LocatedRealComparisonTasteGate_single_carrier_alignment_fields
  field_faithful := LocatedRealComparisonTasteGate_single_carrier_alignment_field_faithful

instance locatedRealComparisonNontrivial : Nontrivial LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedRealComparisonUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealComparisonChapterTasteGate

theorem LocatedRealComparisonTasteGate_e1_row_round_trip
    (L0 L1 W R0 R1 D0 D1 B A H C P N : BHist) :
    LocatedRealComparisonTasteGate_single_carrier_alignment_fromEventFlow
      (LocatedRealComparisonTasteGate_single_carrier_alignment_toEventFlow
        (LocatedRealComparisonUp.mk (BHist.e1 L0) L1 W R0 R1 D0 D1 B A H C P N)) =
      some (LocatedRealComparisonUp.mk (BHist.e1 L0) L1 W R0 R1 D0 D1 B A H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip
    (LocatedRealComparisonUp.mk (BHist.e1 L0) L1 W R0 R1 D0 D1 B A H C P N)

end BEDC.Derived.LocatedRealComparisonUp
