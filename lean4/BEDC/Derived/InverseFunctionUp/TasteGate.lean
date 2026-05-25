import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InverseFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InverseFunctionUp : Type where
  | mk (F B D L K I J S Q R H C P N : BHist) : InverseFunctionUp
  deriving DecidableEq

def inverseFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inverseFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inverseFunctionEncodeBHist h

def inverseFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inverseFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inverseFunctionDecodeBHist tail)

private theorem InverseFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, inverseFunctionDecodeBHist (inverseFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def inverseFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => inverseFunctionEventAtDefault index rest

def inverseFunctionToEventFlow : InverseFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InverseFunctionUp.mk F B D L K I J S Q R H C P N =>
      [inverseFunctionEncodeBHist F,
        inverseFunctionEncodeBHist B,
        inverseFunctionEncodeBHist D,
        inverseFunctionEncodeBHist L,
        inverseFunctionEncodeBHist K,
        inverseFunctionEncodeBHist I,
        inverseFunctionEncodeBHist J,
        inverseFunctionEncodeBHist S,
        inverseFunctionEncodeBHist Q,
        inverseFunctionEncodeBHist R,
        inverseFunctionEncodeBHist H,
        inverseFunctionEncodeBHist C,
        inverseFunctionEncodeBHist P,
        inverseFunctionEncodeBHist N]

def inverseFunctionFromEventFlow (ef : EventFlow) : Option InverseFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (InverseFunctionUp.mk
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 0 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 1 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 2 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 3 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 4 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 5 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 6 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 7 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 8 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 9 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 10 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 11 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 12 ef))
      (inverseFunctionDecodeBHist (inverseFunctionEventAtDefault 13 ef)))

private theorem InverseFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : InverseFunctionUp,
      inverseFunctionFromEventFlow (inverseFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B D L K I J S Q R H C P N =>
      change
        some
          (InverseFunctionUp.mk
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist F))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist B))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist D))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist L))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist K))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist I))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist J))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist S))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist Q))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist R))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist H))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist C))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist P))
            (inverseFunctionDecodeBHist (inverseFunctionEncodeBHist N))) =
          some (InverseFunctionUp.mk F B D L K I J S Q R H C P N)
      rw [InverseFunctionTasteGate_single_carrier_alignment_decode_encode F,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode B,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode D,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode L,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode K,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode I,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode J,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode S,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode Q,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode R,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode H,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode C,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode P,
        InverseFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem InverseFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : InverseFunctionUp} :
    inverseFunctionToEventFlow x = inverseFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inverseFunctionFromEventFlow (inverseFunctionToEventFlow x) =
        inverseFunctionFromEventFlow (inverseFunctionToEventFlow y) :=
    congrArg inverseFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (InverseFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (InverseFunctionTasteGate_single_carrier_alignment_round_trip y)))

private def inverseFunctionFields : InverseFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InverseFunctionUp.mk F B D L K I J S Q R H C P N => [F, B, D, L, K, I, J, S, Q, R, H, C, P, N]

private theorem InverseFunctionTasteGate_single_carrier_alignment_fields :
    ∀ x y : InverseFunctionUp, inverseFunctionFields x = inverseFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 B1 D1 L1 K1 I1 J1 S1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 B2 D2 L2 K2 I2 J2 S2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance inverseFunctionBHistCarrier : BHistCarrier InverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inverseFunctionToEventFlow
  fromEventFlow := inverseFunctionFromEventFlow

instance inverseFunctionChapterTasteGate : ChapterTasteGate InverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inverseFunctionFromEventFlow (inverseFunctionToEventFlow x) = some x
    exact InverseFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (InverseFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance inverseFunctionFieldFaithful : FieldFaithful InverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inverseFunctionFields
  field_faithful := InverseFunctionTasteGate_single_carrier_alignment_fields

instance inverseFunctionNontrivial : BEDC.Meta.TasteGate.Nontrivial InverseFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InverseFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      InverseFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InverseFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inverseFunctionChapterTasteGate

theorem InverseFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, inverseFunctionDecodeBHist (inverseFunctionEncodeBHist h) = h) ∧
      (∀ x : InverseFunctionUp,
        inverseFunctionFromEventFlow (inverseFunctionToEventFlow x) = some x) ∧
        (∀ x y : InverseFunctionUp,
          inverseFunctionToEventFlow x = inverseFunctionToEventFlow y → x = y) ∧
          inverseFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨InverseFunctionTasteGate_single_carrier_alignment_decode_encode,
      InverseFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => InverseFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.InverseFunctionUp
