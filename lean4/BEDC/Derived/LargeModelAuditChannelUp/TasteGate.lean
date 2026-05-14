import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelAuditChannelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelAuditChannelUp : Type where
  | mk : (M Q O C R U V H K P N : BHist) → LargeModelAuditChannelUp
  deriving DecidableEq

def largeModelAuditChannelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelAuditChannelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelAuditChannelEncodeBHist h

def largeModelAuditChannelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelAuditChannelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelAuditChannelDecodeBHist tail)

private theorem largeModelAuditChannelDecode_encode_bhist :
    ∀ h : BHist, largeModelAuditChannelDecodeBHist
      (largeModelAuditChannelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def largeModelAuditChannelToEventFlow : LargeModelAuditChannelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelAuditChannelUp.mk M Q O C R U V H K P N =>
      [[BMark.b0],
        largeModelAuditChannelEncodeBHist M,
        [BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        largeModelAuditChannelEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist N]

def largeModelAuditChannelFromEventFlow : EventFlow → Option LargeModelAuditChannelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | O :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | U :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | V :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | K :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (LargeModelAuditChannelUp.mk
                                                                                                  (largeModelAuditChannelDecodeBHist M)
                                                                                                  (largeModelAuditChannelDecodeBHist Q)
                                                                                                  (largeModelAuditChannelDecodeBHist O)
                                                                                                  (largeModelAuditChannelDecodeBHist C)
                                                                                                  (largeModelAuditChannelDecodeBHist R)
                                                                                                  (largeModelAuditChannelDecodeBHist U)
                                                                                                  (largeModelAuditChannelDecodeBHist V)
                                                                                                  (largeModelAuditChannelDecodeBHist H)
                                                                                                  (largeModelAuditChannelDecodeBHist K)
                                                                                                  (largeModelAuditChannelDecodeBHist P)
                                                                                                  (largeModelAuditChannelDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem largeModelAuditChannel_round_trip :
    ∀ x : LargeModelAuditChannelUp,
      largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M Q O C R U V H K P N =>
      change
        some
          (LargeModelAuditChannelUp.mk
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist M))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist Q))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist O))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist C))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist R))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist U))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist V))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist H))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist K))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist P))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist N))) =
          some (LargeModelAuditChannelUp.mk M Q O C R U V H K P N)
      rw [largeModelAuditChannelDecode_encode_bhist M,
        largeModelAuditChannelDecode_encode_bhist Q,
        largeModelAuditChannelDecode_encode_bhist O,
        largeModelAuditChannelDecode_encode_bhist C,
        largeModelAuditChannelDecode_encode_bhist R,
        largeModelAuditChannelDecode_encode_bhist U,
        largeModelAuditChannelDecode_encode_bhist V,
        largeModelAuditChannelDecode_encode_bhist H,
        largeModelAuditChannelDecode_encode_bhist K,
        largeModelAuditChannelDecode_encode_bhist P,
        largeModelAuditChannelDecode_encode_bhist N]

private theorem largeModelAuditChannelToEventFlow_injective {x y : LargeModelAuditChannelUp} :
    largeModelAuditChannelToEventFlow x = largeModelAuditChannelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) =
        largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow y) :=
    congrArg largeModelAuditChannelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelAuditChannel_round_trip x).symm
      (Eq.trans hread (largeModelAuditChannel_round_trip y)))

instance largeModelAuditChannelBHistCarrier : BHistCarrier LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelAuditChannelToEventFlow
  fromEventFlow := largeModelAuditChannelFromEventFlow

instance largeModelAuditChannelChapterTasteGate : ChapterTasteGate LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) = some x
    exact largeModelAuditChannel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelAuditChannelToEventFlow_injective heq)

instance largeModelAuditChannelFieldFaithful : FieldFaithful LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LargeModelAuditChannelUp.mk M Q O C R U V H K P N =>
        [M, Q, O, C, R, U, V, H, K, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk M1 Q1 O1 C1 R1 U1 V1 H1 K1 P1 N1 =>
        cases y with
        | mk M2 Q2 O2 C2 R2 U2 V2 H2 K2 P2 N2 =>
            cases h
            rfl

instance largeModelAuditChannelNontrivial : Nontrivial LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelAuditChannelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelAuditChannelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LargeModelAuditChannelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelAuditChannelChapterTasteGate

theorem LargeModelAuditChannelTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LargeModelAuditChannelUp) ∧
      (∀ x : LargeModelAuditChannelUp,
        largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) = some x) ∧
      (∀ x y : LargeModelAuditChannelUp,
        largeModelAuditChannelToEventFlow x = largeModelAuditChannelToEventFlow y → x = y) ∧
      largeModelAuditChannelEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨largeModelAuditChannelChapterTasteGate⟩
  · constructor
    · intro x
      change largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) = some x
      exact largeModelAuditChannel_round_trip x
    · constructor
      · intro x y heq
        exact largeModelAuditChannelToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelAuditChannelUp
