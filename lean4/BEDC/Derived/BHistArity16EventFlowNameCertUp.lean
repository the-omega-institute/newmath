import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistArity16EventFlowNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistArity16EventFlowNameCertUp : Type where
  | mk
      (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 : BHist) :
      BHistArity16EventFlowNameCertUp
  deriving DecidableEq

def bHistArity16EventFlowNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistArity16EventFlowNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistArity16EventFlowNameCertEncodeBHist h

def bHistArity16EventFlowNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistArity16EventFlowNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistArity16EventFlowNameCertDecodeBHist tail)

private theorem bHistArity16EventFlowNameCertDecode_encode_bhist :
    ∀ h : BHist,
      bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistArity16EventFlowNameCertFields :
    BHistArity16EventFlowNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity16EventFlowNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13
      R14 R15 =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15]

def bHistArity16EventFlowNameCertToEventFlow :
    BHistArity16EventFlowNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity16EventFlowNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13
      R14 R15 =>
      [[BMark.b1, BMark.b0, BMark.b0, BMark.b0],
        bHistArity16EventFlowNameCertEncodeBHist R0,
        bHistArity16EventFlowNameCertEncodeBHist R1,
        bHistArity16EventFlowNameCertEncodeBHist R2,
        bHistArity16EventFlowNameCertEncodeBHist R3,
        bHistArity16EventFlowNameCertEncodeBHist R4,
        bHistArity16EventFlowNameCertEncodeBHist R5,
        bHistArity16EventFlowNameCertEncodeBHist R6,
        bHistArity16EventFlowNameCertEncodeBHist R7,
        bHistArity16EventFlowNameCertEncodeBHist R8,
        bHistArity16EventFlowNameCertEncodeBHist R9,
        bHistArity16EventFlowNameCertEncodeBHist R10,
        bHistArity16EventFlowNameCertEncodeBHist R11,
        bHistArity16EventFlowNameCertEncodeBHist R12,
        bHistArity16EventFlowNameCertEncodeBHist R13,
        bHistArity16EventFlowNameCertEncodeBHist R14,
        bHistArity16EventFlowNameCertEncodeBHist R15]

private def bHistArity16EventFlowNameCertEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bHistArity16EventFlowNameCertEventAtDefault index rest

def bHistArity16EventFlowNameCertFromEventFlow
    (ef : EventFlow) : Option BHistArity16EventFlowNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BHistArity16EventFlowNameCertUp.mk
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 1 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 2 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 3 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 4 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 5 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 6 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 7 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 8 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 9 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 10 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 11 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 12 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 13 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 14 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 15 ef))
      (bHistArity16EventFlowNameCertDecodeBHist
        (bHistArity16EventFlowNameCertEventAtDefault 16 ef)))

private theorem bHistArity16EventFlowNameCert_round_trip :
    ∀ x : BHistArity16EventFlowNameCertUp,
      bHistArity16EventFlowNameCertFromEventFlow
        (bHistArity16EventFlowNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 =>
      change
        some
          (BHistArity16EventFlowNameCertUp.mk
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R0))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R1))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R2))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R3))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R4))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R5))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R6))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R7))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R8))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R9))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R10))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R11))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R12))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R13))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R14))
            (bHistArity16EventFlowNameCertDecodeBHist
              (bHistArity16EventFlowNameCertEncodeBHist R15))) =
          some
            (BHistArity16EventFlowNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
              R11 R12 R13 R14 R15)
      rw [bHistArity16EventFlowNameCertDecode_encode_bhist R0,
        bHistArity16EventFlowNameCertDecode_encode_bhist R1,
        bHistArity16EventFlowNameCertDecode_encode_bhist R2,
        bHistArity16EventFlowNameCertDecode_encode_bhist R3,
        bHistArity16EventFlowNameCertDecode_encode_bhist R4,
        bHistArity16EventFlowNameCertDecode_encode_bhist R5,
        bHistArity16EventFlowNameCertDecode_encode_bhist R6,
        bHistArity16EventFlowNameCertDecode_encode_bhist R7,
        bHistArity16EventFlowNameCertDecode_encode_bhist R8,
        bHistArity16EventFlowNameCertDecode_encode_bhist R9,
        bHistArity16EventFlowNameCertDecode_encode_bhist R10,
        bHistArity16EventFlowNameCertDecode_encode_bhist R11,
        bHistArity16EventFlowNameCertDecode_encode_bhist R12,
        bHistArity16EventFlowNameCertDecode_encode_bhist R13,
        bHistArity16EventFlowNameCertDecode_encode_bhist R14,
        bHistArity16EventFlowNameCertDecode_encode_bhist R15]

private theorem bHistArity16EventFlowNameCertToEventFlow_injective
    {x y : BHistArity16EventFlowNameCertUp} :
    bHistArity16EventFlowNameCertToEventFlow x =
      bHistArity16EventFlowNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 R101 R111 R121 R131 R141 R151 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 R102 R112 R122 R132 R142 R152 =>
          change
            [[BMark.b1, BMark.b0, BMark.b0, BMark.b0],
              bHistArity16EventFlowNameCertEncodeBHist R01,
              bHistArity16EventFlowNameCertEncodeBHist R11,
              bHistArity16EventFlowNameCertEncodeBHist R21,
              bHistArity16EventFlowNameCertEncodeBHist R31,
              bHistArity16EventFlowNameCertEncodeBHist R41,
              bHistArity16EventFlowNameCertEncodeBHist R51,
              bHistArity16EventFlowNameCertEncodeBHist R61,
              bHistArity16EventFlowNameCertEncodeBHist R71,
              bHistArity16EventFlowNameCertEncodeBHist R81,
              bHistArity16EventFlowNameCertEncodeBHist R91,
              bHistArity16EventFlowNameCertEncodeBHist R101,
              bHistArity16EventFlowNameCertEncodeBHist R111,
              bHistArity16EventFlowNameCertEncodeBHist R121,
              bHistArity16EventFlowNameCertEncodeBHist R131,
              bHistArity16EventFlowNameCertEncodeBHist R141,
              bHistArity16EventFlowNameCertEncodeBHist R151] =
              [[BMark.b1, BMark.b0, BMark.b0, BMark.b0],
                bHistArity16EventFlowNameCertEncodeBHist R02,
                bHistArity16EventFlowNameCertEncodeBHist R12,
                bHistArity16EventFlowNameCertEncodeBHist R22,
                bHistArity16EventFlowNameCertEncodeBHist R32,
                bHistArity16EventFlowNameCertEncodeBHist R42,
                bHistArity16EventFlowNameCertEncodeBHist R52,
                bHistArity16EventFlowNameCertEncodeBHist R62,
                bHistArity16EventFlowNameCertEncodeBHist R72,
                bHistArity16EventFlowNameCertEncodeBHist R82,
                bHistArity16EventFlowNameCertEncodeBHist R92,
                bHistArity16EventFlowNameCertEncodeBHist R102,
                bHistArity16EventFlowNameCertEncodeBHist R112,
                bHistArity16EventFlowNameCertEncodeBHist R122,
                bHistArity16EventFlowNameCertEncodeBHist R132,
                bHistArity16EventFlowNameCertEncodeBHist R142,
                bHistArity16EventFlowNameCertEncodeBHist R152] at heq
          injection heq with _ tail0
          injection tail0 with h0 tail1
          injection tail1 with h1 tail2
          injection tail2 with h2 tail3
          injection tail3 with h3 tail4
          injection tail4 with h4 tail5
          injection tail5 with h5 tail6
          injection tail6 with h6 tail7
          injection tail7 with h7 tail8
          injection tail8 with h8 tail9
          injection tail9 with h9 tail10
          injection tail10 with h10 tail11
          injection tail11 with h11 tail12
          injection tail12 with h12 tail13
          injection tail13 with h13 tail14
          injection tail14 with h14 tail15
          injection tail15 with h15 _
          have e0 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R01) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R02) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h0
          have e1 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R11) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R12) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h1
          have e2 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R21) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R22) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h2
          have e3 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R31) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R32) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h3
          have e4 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R41) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R42) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h4
          have e5 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R51) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R52) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h5
          have e6 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R61) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R62) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h6
          have e7 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R71) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R72) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h7
          have e8 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R81) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R82) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h8
          have e9 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R91) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R92) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h9
          have e10 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R101) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R102) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h10
          have e11 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R111) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R112) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h11
          have e12 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R121) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R122) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h12
          have e13 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R131) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R132) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h13
          have e14 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R141) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R142) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h14
          have e15 :
              bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R151) =
                bHistArity16EventFlowNameCertDecodeBHist
                  (bHistArity16EventFlowNameCertEncodeBHist R152) := congrArg
            bHistArity16EventFlowNameCertDecodeBHist h15
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R01,
            bHistArity16EventFlowNameCertDecode_encode_bhist R02] at e0
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R11,
            bHistArity16EventFlowNameCertDecode_encode_bhist R12] at e1
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R21,
            bHistArity16EventFlowNameCertDecode_encode_bhist R22] at e2
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R31,
            bHistArity16EventFlowNameCertDecode_encode_bhist R32] at e3
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R41,
            bHistArity16EventFlowNameCertDecode_encode_bhist R42] at e4
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R51,
            bHistArity16EventFlowNameCertDecode_encode_bhist R52] at e5
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R61,
            bHistArity16EventFlowNameCertDecode_encode_bhist R62] at e6
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R71,
            bHistArity16EventFlowNameCertDecode_encode_bhist R72] at e7
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R81,
            bHistArity16EventFlowNameCertDecode_encode_bhist R82] at e8
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R91,
            bHistArity16EventFlowNameCertDecode_encode_bhist R92] at e9
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R101,
            bHistArity16EventFlowNameCertDecode_encode_bhist R102] at e10
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R111,
            bHistArity16EventFlowNameCertDecode_encode_bhist R112] at e11
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R121,
            bHistArity16EventFlowNameCertDecode_encode_bhist R122] at e12
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R131,
            bHistArity16EventFlowNameCertDecode_encode_bhist R132] at e13
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R141,
            bHistArity16EventFlowNameCertDecode_encode_bhist R142] at e14
          rw [bHistArity16EventFlowNameCertDecode_encode_bhist R151,
            bHistArity16EventFlowNameCertDecode_encode_bhist R152] at e15
          cases e0
          cases e1
          cases e2
          cases e3
          cases e4
          cases e5
          cases e6
          cases e7
          cases e8
          cases e9
          cases e10
          cases e11
          cases e12
          cases e13
          cases e14
          cases e15
          rfl

private theorem bHistArity16EventFlowNameCert_fields_faithful :
    ∀ x y : BHistArity16EventFlowNameCertUp,
      bHistArity16EventFlowNameCertFields x =
        bHistArity16EventFlowNameCertFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 R101 R111 R121 R131 R141 R151 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 R102 R112 R122 R132 R142 R152 =>
          cases hfields
          rfl

instance bHistArity16EventFlowNameCertBHistCarrier :
    BHistCarrier BHistArity16EventFlowNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistArity16EventFlowNameCertToEventFlow
  fromEventFlow := bHistArity16EventFlowNameCertFromEventFlow

instance bHistArity16EventFlowNameCertChapterTasteGate :
    ChapterTasteGate BHistArity16EventFlowNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistArity16EventFlowNameCertFromEventFlow
        (bHistArity16EventFlowNameCertToEventFlow x) = some x
    exact bHistArity16EventFlowNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistArity16EventFlowNameCertToEventFlow_injective heq)

instance bHistArity16EventFlowNameCertFieldFaithful :
    FieldFaithful BHistArity16EventFlowNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistArity16EventFlowNameCertFields
  field_faithful := bHistArity16EventFlowNameCert_fields_faithful

instance bHistArity16EventFlowNameCertNontrivial :
    Nontrivial BHistArity16EventFlowNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistArity16EventFlowNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BHistArity16EventFlowNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BHistArity16EventFlowNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistArity16EventFlowNameCertChapterTasteGate

theorem BHistArity16EventFlowNameCertTasteGate_single_carrier_alignment :
    (forall h : BHist,
        bHistArity16EventFlowNameCertDecodeBHist
          (bHistArity16EventFlowNameCertEncodeBHist h) = h) ∧
      (forall x : BHistArity16EventFlowNameCertUp,
        bHistArity16EventFlowNameCertFromEventFlow
          (bHistArity16EventFlowNameCertToEventFlow x) = some x) ∧
      (forall x y : BHistArity16EventFlowNameCertUp,
        bHistArity16EventFlowNameCertToEventFlow x =
          bHistArity16EventFlowNameCertToEventFlow y -> x = y) ∧
      bHistArity16EventFlowNameCertFields
          (BHistArity16EventFlowNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact bHistArity16EventFlowNameCertDecode_encode_bhist
  constructor
  ·
    intro x
    cases x with
    | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 =>
        change
          some
            (BHistArity16EventFlowNameCertUp.mk
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R0))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R1))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R2))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R3))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R4))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R5))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R6))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R7))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R8))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R9))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R10))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R11))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R12))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R13))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R14))
              (bHistArity16EventFlowNameCertDecodeBHist
                (bHistArity16EventFlowNameCertEncodeBHist R15))) =
            some
              (BHistArity16EventFlowNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9
                R10 R11 R12 R13 R14 R15)
        rw [bHistArity16EventFlowNameCertDecode_encode_bhist R0,
          bHistArity16EventFlowNameCertDecode_encode_bhist R1,
          bHistArity16EventFlowNameCertDecode_encode_bhist R2,
          bHistArity16EventFlowNameCertDecode_encode_bhist R3,
          bHistArity16EventFlowNameCertDecode_encode_bhist R4,
          bHistArity16EventFlowNameCertDecode_encode_bhist R5,
          bHistArity16EventFlowNameCertDecode_encode_bhist R6,
          bHistArity16EventFlowNameCertDecode_encode_bhist R7,
          bHistArity16EventFlowNameCertDecode_encode_bhist R8,
          bHistArity16EventFlowNameCertDecode_encode_bhist R9,
          bHistArity16EventFlowNameCertDecode_encode_bhist R10,
          bHistArity16EventFlowNameCertDecode_encode_bhist R11,
          bHistArity16EventFlowNameCertDecode_encode_bhist R12,
          bHistArity16EventFlowNameCertDecode_encode_bhist R13,
          bHistArity16EventFlowNameCertDecode_encode_bhist R14,
          bHistArity16EventFlowNameCertDecode_encode_bhist R15]
  constructor
  ·
    intro x y heq
    exact bHistArity16EventFlowNameCertToEventFlow_injective heq
  · rfl

end BEDC.Derived.BHistArity16EventFlowNameCertUp
