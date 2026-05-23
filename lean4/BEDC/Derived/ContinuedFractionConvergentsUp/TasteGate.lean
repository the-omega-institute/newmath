import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuedFractionConvergentsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuedFractionConvergentsUp : Type where
  | mk (A N D Q W E R S H C P L : BHist) : ContinuedFractionConvergentsUp
  deriving DecidableEq

def continuedFractionConvergentsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuedFractionConvergentsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuedFractionConvergentsEncodeBHist h

def continuedFractionConvergentsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuedFractionConvergentsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuedFractionConvergentsDecodeBHist tail)

private theorem ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      continuedFractionConvergentsDecodeBHist
          (continuedFractionConvergentsEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuedFractionConvergentsFields : ContinuedFractionConvergentsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuedFractionConvergentsUp.mk A N D Q W E R S H C P L =>
      [A, N, D, Q, W, E, R, S, H, C, P, L]

def continuedFractionConvergentsToEventFlow : ContinuedFractionConvergentsUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (continuedFractionConvergentsFields x).map continuedFractionConvergentsEncodeBHist

private def continuedFractionConvergentsEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuedFractionConvergentsEventAtDefault index rest

def continuedFractionConvergentsFromEventFlow
    (ef : EventFlow) : Option ContinuedFractionConvergentsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuedFractionConvergentsUp.mk
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 0 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 1 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 2 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 3 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 4 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 5 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 6 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 7 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 8 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 9 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 10 ef))
      (continuedFractionConvergentsDecodeBHist
        (continuedFractionConvergentsEventAtDefault 11 ef)))

private theorem ContinuedFractionConvergentsTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContinuedFractionConvergentsUp,
      continuedFractionConvergentsFromEventFlow
          (continuedFractionConvergentsToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A N D Q W E R S H C P L =>
      change
        some
            (ContinuedFractionConvergentsUp.mk
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist A))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist N))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist D))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist Q))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist W))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist E))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist R))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist S))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist H))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist C))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist P))
              (continuedFractionConvergentsDecodeBHist
                (continuedFractionConvergentsEncodeBHist L))) =
          some (ContinuedFractionConvergentsUp.mk A N D Q W E R S H C P L)
      rw [ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode A,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode N,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode D,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode Q,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode W,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode E,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode R,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode S,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode H,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode C,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode P,
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode L]

private theorem ContinuedFractionConvergentsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuedFractionConvergentsUp} :
    continuedFractionConvergentsToEventFlow x =
        continuedFractionConvergentsToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuedFractionConvergentsFromEventFlow
          (continuedFractionConvergentsToEventFlow x) =
        continuedFractionConvergentsFromEventFlow
          (continuedFractionConvergentsToEventFlow y) :=
    congrArg continuedFractionConvergentsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContinuedFractionConvergentsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContinuedFractionConvergentsTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContinuedFractionConvergentsTasteGate_single_carrier_alignment_fields :
    ∀ x y : ContinuedFractionConvergentsUp,
      continuedFractionConvergentsFields x = continuedFractionConvergentsFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 N1 D1 Q1 W1 E1 R1 S1 H1 C1 P1 L1 =>
      cases y with
      | mk A2 N2 D2 Q2 W2 E2 R2 S2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance continuedFractionConvergentsBHistCarrier :
    BHistCarrier ContinuedFractionConvergentsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuedFractionConvergentsToEventFlow
  fromEventFlow := continuedFractionConvergentsFromEventFlow

instance continuedFractionConvergentsChapterTasteGate :
    ChapterTasteGate ContinuedFractionConvergentsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      continuedFractionConvergentsFromEventFlow
          (continuedFractionConvergentsToEventFlow x) =
        some x
    exact ContinuedFractionConvergentsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ContinuedFractionConvergentsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance continuedFractionConvergentsFieldFaithful :
    FieldFaithful ContinuedFractionConvergentsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := continuedFractionConvergentsFields
  field_faithful := ContinuedFractionConvergentsTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate ContinuedFractionConvergentsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuedFractionConvergentsChapterTasteGate

theorem ContinuedFractionConvergentsTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      continuedFractionConvergentsDecodeBHist (continuedFractionConvergentsEncodeBHist h) = h) ∧
      (∀ x : ContinuedFractionConvergentsUp,
        continuedFractionConvergentsFromEventFlow
            (continuedFractionConvergentsToEventFlow x) =
          some x) ∧
        (∀ x y : ContinuedFractionConvergentsUp,
          continuedFractionConvergentsToEventFlow x =
              continuedFractionConvergentsToEventFlow y →
            x = y) ∧
          continuedFractionConvergentsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨ContinuedFractionConvergentsTasteGate_single_carrier_alignment_decode,
      ContinuedFractionConvergentsTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ContinuedFractionConvergentsTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContinuedFractionConvergentsUp
