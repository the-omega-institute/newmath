import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSeriesRatioTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSeriesRatioTestUp : Type where
  | mk (S T B W R E H C P N : BHist) : RealSeriesRatioTestUp
  deriving DecidableEq

def RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist h

def RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
        (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def RealSeriesRatioTestTasteGate_single_carrier_alignment_fields :
    RealSeriesRatioTestUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSeriesRatioTestUp.mk S T B W R E H C P N =>
      [S, T, B, W, R, E, H, C, P, N]

def RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow :
    RealSeriesRatioTestUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (RealSeriesRatioTestTasteGate_single_carrier_alignment_fields x).map
        RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist

def RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option RealSeriesRatioTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (RealSeriesRatioTestUp.mk
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    S)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    T)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    B)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    W)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    R)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    E)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    H)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    C)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    P)
                                                  (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
                                                    N))
                                          | _ :: _ => none

private theorem RealSeriesRatioTestTasteGate_single_carrier_alignment_round_trip :
    forall x : RealSeriesRatioTestUp,
      RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow
        (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T B W R E H C P N =>
      change
        some
          (RealSeriesRatioTestUp.mk
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist S))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist T))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist B))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist W))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist R))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist E))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist H))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist C))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist P))
            (RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
              (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RealSeriesRatioTestUp.mk S T B W R E H C P N)
      rw [RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode S,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode T,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode B,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode W,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode R,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode E,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode H,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode C,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode P,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSeriesRatioTestUp} :
    RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow x =
      RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow
          (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow x) =
        RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow
          (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealSeriesRatioTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealSeriesRatioTestTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealSeriesRatioTestTasteGate_single_carrier_alignment_field_faithful :
    forall x y : RealSeriesRatioTestUp,
      RealSeriesRatioTestTasteGate_single_carrier_alignment_fields x =
        RealSeriesRatioTestTasteGate_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 B1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 B2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realSeriesRatioTestBHistCarrier : BHistCarrier RealSeriesRatioTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow

instance realSeriesRatioTestChapterTasteGateInstance :
    ChapterTasteGate RealSeriesRatioTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow
        (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact RealSeriesRatioTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realSeriesRatioTestFieldFaithful :
    FieldFaithful RealSeriesRatioTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RealSeriesRatioTestTasteGate_single_carrier_alignment_fields
  field_faithful := RealSeriesRatioTestTasteGate_single_carrier_alignment_field_faithful

instance realSeriesRatioTestNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealSeriesRatioTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSeriesRatioTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealSeriesRatioTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def realSeriesRatioTestChapterTasteGate :
    ChapterTasteGate RealSeriesRatioTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  { round_trip := by
      intro x
      change
        RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow
          (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow x) = some x
      exact RealSeriesRatioTestTasteGate_single_carrier_alignment_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy
        (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow_injective heq) }

theorem RealSeriesRatioTestTasteGate_single_carrier_alignment :
    (forall h : BHist,
      RealSeriesRatioTestTasteGate_single_carrier_alignment_decodeBHist
        (RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      (forall x : RealSeriesRatioTestUp,
        RealSeriesRatioTestTasteGate_single_carrier_alignment_fromEventFlow
          (RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow x) = some x) ∧
        (forall x y : RealSeriesRatioTestUp,
          RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow x =
            RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow y -> x = y) ∧
          RealSeriesRatioTestTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealSeriesRatioTestTasteGate_single_carrier_alignment_decode_encode,
      RealSeriesRatioTestTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RealSeriesRatioTestTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealSeriesRatioTestUp
