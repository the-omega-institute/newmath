import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperfunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperfunctionUp : Type where
  | mk
      (T O B S Q A R D E K L M C P N : BHist) : HyperfunctionUp
  deriving DecidableEq

def hyperfunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperfunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperfunctionEncodeBHist h

def hyperfunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperfunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperfunctionDecodeBHist tail)

private theorem HyperfunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hyperfunctionDecodeBHist (hyperfunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hyperfunctionFields : HyperfunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperfunctionUp.mk T O B S Q A R D E K L M C P N =>
      [T, O, B, S, Q, A, R, D, E, K, L, M, C, P, N]

def hyperfunctionToEventFlow : HyperfunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperfunctionFields x).map hyperfunctionEncodeBHist

private def hyperfunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperfunctionEventAtDefault index rest

def hyperfunctionFromEventFlow (ef : EventFlow) : Option HyperfunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperfunctionUp.mk
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 0 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 1 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 2 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 3 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 4 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 5 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 6 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 7 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 8 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 9 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 10 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 11 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 12 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 13 ef))
      (hyperfunctionDecodeBHist (hyperfunctionEventAtDefault 14 ef)))

private theorem HyperfunctionTasteGate_single_carrier_alignment_round_trip
    (x : HyperfunctionUp) :
    hyperfunctionFromEventFlow (hyperfunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T O B S Q A R D E K L M C P N =>
      change
        some
          (HyperfunctionUp.mk
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist T))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist O))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist B))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist S))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist Q))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist A))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist R))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist D))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist E))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist K))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist L))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist M))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist C))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist P))
            (hyperfunctionDecodeBHist (hyperfunctionEncodeBHist N))) =
          some (HyperfunctionUp.mk T O B S Q A R D E K L M C P N)
      rw [HyperfunctionTasteGate_single_carrier_alignment_decode_encode T,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode O,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode B,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode S,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode Q,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode A,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode R,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode D,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode E,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode K,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode L,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode M,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode C,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode P,
        HyperfunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperfunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperfunctionUp} :
    hyperfunctionToEventFlow x = hyperfunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperfunctionFromEventFlow (hyperfunctionToEventFlow x) =
        hyperfunctionFromEventFlow (hyperfunctionToEventFlow y) :=
    congrArg hyperfunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HyperfunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HyperfunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperfunctionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : HyperfunctionUp, hyperfunctionFields x = hyperfunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 O1 B1 S1 Q1 A1 R1 D1 E1 K1 L1 M1 C1 P1 N1 =>
      cases y with
      | mk T2 O2 B2 S2 Q2 A2 R2 D2 E2 K2 L2 M2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperfunctionBHistCarrier : BHistCarrier HyperfunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperfunctionToEventFlow
  fromEventFlow := hyperfunctionFromEventFlow

instance hyperfunctionChapterTasteGate : ChapterTasteGate HyperfunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperfunctionFromEventFlow (hyperfunctionToEventFlow x) = some x
    exact HyperfunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperfunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HyperfunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, hyperfunctionDecodeBHist (hyperfunctionEncodeBHist h) = h) ∧
      (∀ x : HyperfunctionUp,
        hyperfunctionFromEventFlow (hyperfunctionToEventFlow x) = some x) ∧
        (∀ x y : HyperfunctionUp,
          hyperfunctionToEventFlow x = hyperfunctionToEventFlow y → x = y) ∧
          hyperfunctionEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : HyperfunctionUp, hyperfunctionFields x = hyperfunctionFields y → x = y) ∧
              (∃ x y : HyperfunctionUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HyperfunctionTasteGate_single_carrier_alignment_decode_encode,
      HyperfunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HyperfunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      HyperfunctionTasteGate_single_carrier_alignment_fields_faithful,
      ⟨HyperfunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        HyperfunctionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.HyperfunctionUp.TasteGate
