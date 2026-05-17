import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SocketReportUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SocketReportUp : Type where
  | mk (S U K G H C P N : BHist) : SocketReportUp
  deriving DecidableEq

def socketReportEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: socketReportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: socketReportEncodeBHist h

def socketReportDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (socketReportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (socketReportDecodeBHist tail)

private theorem socketReportDecode_encode_bhist :
    forall h : BHist, socketReportDecodeBHist (socketReportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def socketReportFields : SocketReportUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SocketReportUp.mk S U K G H C P N => [S, U, K, G, H, C, P, N]

def socketReportToEventFlow : SocketReportUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (socketReportFields x).map socketReportEncodeBHist

def socketReportFromEventFlow : EventFlow -> Option SocketReportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | U :: rest1 =>
          match rest1 with
          | [] => none
          | K :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (SocketReportUp.mk
                                          (socketReportDecodeBHist S)
                                          (socketReportDecodeBHist U)
                                          (socketReportDecodeBHist K)
                                          (socketReportDecodeBHist G)
                                          (socketReportDecodeBHist H)
                                          (socketReportDecodeBHist C)
                                          (socketReportDecodeBHist P)
                                          (socketReportDecodeBHist N))
                                  | _ :: _ => none

private theorem socketReport_round_trip :
    forall x : SocketReportUp,
      socketReportFromEventFlow (socketReportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S U K G H C P N =>
      change
        some
          (SocketReportUp.mk
            (socketReportDecodeBHist (socketReportEncodeBHist S))
            (socketReportDecodeBHist (socketReportEncodeBHist U))
            (socketReportDecodeBHist (socketReportEncodeBHist K))
            (socketReportDecodeBHist (socketReportEncodeBHist G))
            (socketReportDecodeBHist (socketReportEncodeBHist H))
            (socketReportDecodeBHist (socketReportEncodeBHist C))
            (socketReportDecodeBHist (socketReportEncodeBHist P))
            (socketReportDecodeBHist (socketReportEncodeBHist N))) =
          some (SocketReportUp.mk S U K G H C P N)
      rw [socketReportDecode_encode_bhist S, socketReportDecode_encode_bhist U,
        socketReportDecode_encode_bhist K, socketReportDecode_encode_bhist G,
        socketReportDecode_encode_bhist H, socketReportDecode_encode_bhist C,
        socketReportDecode_encode_bhist P, socketReportDecode_encode_bhist N]

private theorem socketReportToEventFlow_injective
    {x y : SocketReportUp} :
    socketReportToEventFlow x = socketReportToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      socketReportFromEventFlow (socketReportToEventFlow x) =
        socketReportFromEventFlow (socketReportToEventFlow y) :=
    congrArg socketReportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (socketReport_round_trip x).symm
      (Eq.trans hread (socketReport_round_trip y)))

private theorem socketReport_fields_faithful :
    forall x y : SocketReportUp, socketReportFields x = socketReportFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 U1 K1 G1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 U2 K2 G2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance socketReportBHistCarrier : BHistCarrier SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := socketReportToEventFlow
  fromEventFlow := socketReportFromEventFlow

instance socketReportChapterTasteGate : ChapterTasteGate SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change socketReportFromEventFlow (socketReportToEventFlow x) = some x
    exact socketReport_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (socketReportToEventFlow_injective heq)

instance socketReportFieldFaithful : FieldFaithful SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := socketReportFields
  field_faithful := socketReport_fields_faithful

instance socketReportNontrivial : Nontrivial SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SocketReportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      SocketReportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SocketReportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  socketReportChapterTasteGate

theorem SocketReportTasteGate_single_carrier_alignment :
    (forall h : BHist, socketReportDecodeBHist (socketReportEncodeBHist h) = h) ∧
      (forall x : SocketReportUp,
        socketReportFromEventFlow (socketReportToEventFlow x) = some x) ∧
        (forall x y : SocketReportUp,
          socketReportToEventFlow x = socketReportToEventFlow y -> x = y) ∧
          socketReportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk S U K G H C P N =>
          change
            some
              (SocketReportUp.mk
                (socketReportDecodeBHist (socketReportEncodeBHist S))
                (socketReportDecodeBHist (socketReportEncodeBHist U))
                (socketReportDecodeBHist (socketReportEncodeBHist K))
                (socketReportDecodeBHist (socketReportEncodeBHist G))
                (socketReportDecodeBHist (socketReportEncodeBHist H))
                (socketReportDecodeBHist (socketReportEncodeBHist C))
                (socketReportDecodeBHist (socketReportEncodeBHist P))
                (socketReportDecodeBHist (socketReportEncodeBHist N))) =
              some (SocketReportUp.mk S U K G H C P N)
          rw [socketReportDecode_encode_bhist S, socketReportDecode_encode_bhist U,
            socketReportDecode_encode_bhist K, socketReportDecode_encode_bhist G,
            socketReportDecode_encode_bhist H, socketReportDecode_encode_bhist C,
            socketReportDecode_encode_bhist P, socketReportDecode_encode_bhist N]
    · constructor
      · intro x y heq
        have hread :
            socketReportFromEventFlow (socketReportToEventFlow x) =
              socketReportFromEventFlow (socketReportToEventFlow y) :=
          congrArg socketReportFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (socketReport_round_trip x).symm
            (Eq.trans hread (socketReport_round_trip y)))
      · rfl

end BEDC.Derived.SocketReportUp.TasteGate
