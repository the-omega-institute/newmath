import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AsymptoticEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AsymptoticEquivalenceUp : Type where
  | mk (S0 S1 R0 R1 D T E H C P N : BHist) : AsymptoticEquivalenceUp
  deriving DecidableEq

def asymptoticEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: asymptoticEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: asymptoticEquivalenceEncodeBHist h

def asymptoticEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (asymptoticEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (asymptoticEquivalenceDecodeBHist tail)

private theorem AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def asymptoticEquivalenceFields : AsymptoticEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AsymptoticEquivalenceUp.mk S0 S1 R0 R1 D T E H C P N =>
      [S0, S1, R0, R1, D, T, E, H, C, P, N]

def asymptoticEquivalenceToEventFlow : AsymptoticEquivalenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (asymptoticEquivalenceFields x).map asymptoticEquivalenceEncodeBHist

private def asymptoticEquivalenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => asymptoticEquivalenceEventAtDefault index rest

def asymptoticEquivalenceFromEventFlow (ef : EventFlow) : Option AsymptoticEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AsymptoticEquivalenceUp.mk
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 0 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 1 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 2 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 3 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 4 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 5 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 6 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 7 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 8 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 9 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAtDefault 10 ef)))

private theorem AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AsymptoticEquivalenceUp,
      asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 R0 R1 D T E H C P N =>
      change
        some
            (AsymptoticEquivalenceUp.mk
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist S0))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist S1))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist R0))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist R1))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist D))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist T))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist E))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist H))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist C))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist P))
              (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist N))) =
          some (AsymptoticEquivalenceUp.mk S0 S1 R0 R1 D T E H C P N)
      rw [AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode S0,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode S1,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode R0,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode R1,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode D,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode T,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode E,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode H,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode C,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode P,
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode N]

private theorem AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AsymptoticEquivalenceUp} :
    asymptoticEquivalenceToEventFlow x = asymptoticEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) =
        asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow y) :=
    congrArg asymptoticEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : AsymptoticEquivalenceUp,
      asymptoticEquivalenceFields x = asymptoticEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S01 S11 R01 R11 D1 T1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S02 S12 R02 R12 D2 T2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance asymptoticEquivalenceBHistCarrier : BHistCarrier AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := asymptoticEquivalenceToEventFlow
  fromEventFlow := asymptoticEquivalenceFromEventFlow

instance asymptoticEquivalenceChapterTasteGate :
    ChapterTasteGate AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) =
      some x
    exact AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance asymptoticEquivalenceFieldFaithful : FieldFaithful AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := asymptoticEquivalenceFields
  field_faithful := AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_fields

instance asymptoticEquivalenceNontrivial : Nontrivial AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AsymptoticEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AsymptoticEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AsymptoticEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  asymptoticEquivalenceChapterTasteGate

theorem AsymptoticEquivalenceUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h) ∧
      (∀ x : AsymptoticEquivalenceUp,
        asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) =
          some x) ∧
        (∀ x y : AsymptoticEquivalenceUp,
          asymptoticEquivalenceToEventFlow x = asymptoticEquivalenceToEventFlow y →
            x = y) ∧
          asymptoticEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_decode,
      AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AsymptoticEquivalenceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AsymptoticEquivalenceUp
