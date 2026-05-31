import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KummerTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KummerTestUp : Type where
  | mk (A Q U D T R E H C P N : BHist) : KummerTestUp
  deriving DecidableEq

def kummerTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kummerTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kummerTestEncodeBHist h

def kummerTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kummerTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kummerTestDecodeBHist tail)

private theorem KummerTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kummerTestDecodeBHist (kummerTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def kummerTestEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kummerTestEventAtDefault index rest

def kummerTestToEventFlow : KummerTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KummerTestUp.mk A Q U D T R E H C P N =>
      [kummerTestEncodeBHist A,
        kummerTestEncodeBHist Q,
        kummerTestEncodeBHist U,
        kummerTestEncodeBHist D,
        kummerTestEncodeBHist T,
        kummerTestEncodeBHist R,
        kummerTestEncodeBHist E,
        kummerTestEncodeBHist H,
        kummerTestEncodeBHist C,
        kummerTestEncodeBHist P,
        kummerTestEncodeBHist N]

def kummerTestFromEventFlow (ef : EventFlow) : Option KummerTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KummerTestUp.mk
      (kummerTestDecodeBHist (kummerTestEventAtDefault 0 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 1 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 2 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 3 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 4 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 5 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 6 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 7 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 8 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 9 ef))
      (kummerTestDecodeBHist (kummerTestEventAtDefault 10 ef)))

private theorem KummerTestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KummerTestUp, kummerTestFromEventFlow (kummerTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q U D T R E H C P N =>
      change
        some
          (KummerTestUp.mk
            (kummerTestDecodeBHist (kummerTestEncodeBHist A))
            (kummerTestDecodeBHist (kummerTestEncodeBHist Q))
            (kummerTestDecodeBHist (kummerTestEncodeBHist U))
            (kummerTestDecodeBHist (kummerTestEncodeBHist D))
            (kummerTestDecodeBHist (kummerTestEncodeBHist T))
            (kummerTestDecodeBHist (kummerTestEncodeBHist R))
            (kummerTestDecodeBHist (kummerTestEncodeBHist E))
            (kummerTestDecodeBHist (kummerTestEncodeBHist H))
            (kummerTestDecodeBHist (kummerTestEncodeBHist C))
            (kummerTestDecodeBHist (kummerTestEncodeBHist P))
            (kummerTestDecodeBHist (kummerTestEncodeBHist N))) =
          some (KummerTestUp.mk A Q U D T R E H C P N)
      rw [KummerTestTasteGate_single_carrier_alignment_decode_encode A,
        KummerTestTasteGate_single_carrier_alignment_decode_encode Q,
        KummerTestTasteGate_single_carrier_alignment_decode_encode U,
        KummerTestTasteGate_single_carrier_alignment_decode_encode D,
        KummerTestTasteGate_single_carrier_alignment_decode_encode T,
        KummerTestTasteGate_single_carrier_alignment_decode_encode R,
        KummerTestTasteGate_single_carrier_alignment_decode_encode E,
        KummerTestTasteGate_single_carrier_alignment_decode_encode H,
        KummerTestTasteGate_single_carrier_alignment_decode_encode C,
        KummerTestTasteGate_single_carrier_alignment_decode_encode P,
        KummerTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem KummerTestTasteGate_single_carrier_alignment_toEventFlow_injective {x y : KummerTestUp} :
    kummerTestToEventFlow x = kummerTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kummerTestFromEventFlow (kummerTestToEventFlow x) =
        kummerTestFromEventFlow (kummerTestToEventFlow y) :=
    congrArg kummerTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KummerTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KummerTestTasteGate_single_carrier_alignment_round_trip y)))

private def kummerTestFields : KummerTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KummerTestUp.mk A Q U D T R E H C P N => [A, Q, U, D, T, R, E, H, C, P, N]

private theorem KummerTestTasteGate_single_carrier_alignment_fields :
    ∀ x y : KummerTestUp, kummerTestFields x = kummerTestFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 Q1 U1 D1 T1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 Q2 U2 D2 T2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance kummerTestBHistCarrier : BHistCarrier KummerTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kummerTestToEventFlow
  fromEventFlow := kummerTestFromEventFlow

instance kummerTestChapterTasteGate : ChapterTasteGate KummerTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kummerTestFromEventFlow (kummerTestToEventFlow x) = some x
    exact KummerTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KummerTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kummerTestFieldFaithful : FieldFaithful KummerTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kummerTestFields
  field_faithful := KummerTestTasteGate_single_carrier_alignment_fields

instance kummerTestNontrivial : BEDC.Meta.TasteGate.Nontrivial KummerTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KummerTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KummerTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KummerTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kummerTestChapterTasteGate

theorem KummerTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, kummerTestDecodeBHist (kummerTestEncodeBHist h) = h) ∧
      (∀ x : KummerTestUp, kummerTestFromEventFlow (kummerTestToEventFlow x) = some x) ∧
        (∀ x y : KummerTestUp,
          kummerTestToEventFlow x = kummerTestToEventFlow y → x = y) ∧
          kummerTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨KummerTestTasteGate_single_carrier_alignment_decode_encode,
      KummerTestTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => KummerTestTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KummerTestUp
