import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealOrderUp : Type where
  | mk : (S T W D Q R A H C P N : BHist) -> CauchyRealOrderUp
  deriving DecidableEq

def CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist h

def CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
        (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CauchyRealOrderTasteGate_single_carrier_alignment_fields :
    CauchyRealOrderUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealOrderUp.mk S T W D Q R A H C P N => [S, T, W, D, Q, R, A, H, C, P, N]

def CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow :
    CauchyRealOrderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CauchyRealOrderTasteGate_single_carrier_alignment_fields x).map
        CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist

def CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option CauchyRealOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | A :: rest6 =>
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
                                                    (CauchyRealOrderUp.mk
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist S)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist T)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist W)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist D)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist Q)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist R)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist A)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist H)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist C)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist P)
                                                      (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist N))
                                              | _ :: _ => none

private theorem CauchyRealOrderTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyRealOrderUp,
      CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W D Q R A H C P N =>
      change
        some
          (CauchyRealOrderUp.mk
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist S))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist T))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist W))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist Q))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist R))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist A))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist H))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyRealOrderTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealOrderTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyRealOrderUp.mk S T W D Q R A H C P N)
      rw [CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode S,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode T,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode W,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode R,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode A,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealOrderUp} :
    CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow x =
      CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      some x = some y := by
    calc
      some x =
          CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CauchyRealOrderTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y :=
        CauchyRealOrderTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hread

private theorem CauchyRealOrderTasteGate_single_carrier_alignment_field_faithful :
    forall x y : CauchyRealOrderUp,
      CauchyRealOrderTasteGate_single_carrier_alignment_fields x =
        CauchyRealOrderTasteGate_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 W1 D1 Q1 R1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 W2 D2 Q2 R2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyRealOrderBHistCarrier : BHistCarrier CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow

instance cauchyRealOrderChapterTasteGate : ChapterTasteGate CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact CauchyRealOrderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRealOrderFieldFaithful : FieldFaithful CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyRealOrderTasteGate_single_carrier_alignment_fields
  field_faithful := CauchyRealOrderTasteGate_single_carrier_alignment_field_faithful

instance cauchyRealOrderNontrivial : Nontrivial CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealOrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRealOrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRealOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealOrderChapterTasteGate

theorem CauchyRealOrderTasteGate_e0_row_round_trip
    (S T W D Q R A H C P N : BHist) :
    CauchyRealOrderTasteGate_single_carrier_alignment_fromEventFlow
      (CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow
        (CauchyRealOrderUp.mk (BHist.e0 S) T W D Q R A H C P N)) =
      some (CauchyRealOrderUp.mk (BHist.e0 S) T W D Q R A H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact CauchyRealOrderTasteGate_single_carrier_alignment_round_trip
    (CauchyRealOrderUp.mk (BHist.e0 S) T W D Q R A H C P N)

end BEDC.Derived.CauchyRealOrderUp
