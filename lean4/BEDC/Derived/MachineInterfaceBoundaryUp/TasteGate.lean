import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineInterfaceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineInterfaceBoundaryUp : Type where
  | mk (R E F A S H C P N : BHist) : MachineInterfaceBoundaryUp
  deriving DecidableEq

def machineInterfaceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: machineInterfaceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: machineInterfaceBoundaryEncodeBHist h

def machineInterfaceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (machineInterfaceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (machineInterfaceBoundaryDecodeBHist tail)

private theorem machineInterfaceBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def machineInterfaceBoundaryFields : MachineInterfaceBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MachineInterfaceBoundaryUp.mk R E F A S H C P N => [R, E, F, A, S, H, C, P, N]

def machineInterfaceBoundaryToEventFlow : MachineInterfaceBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MachineInterfaceBoundaryUp.mk R E F A S H C P N =>
      [machineInterfaceBoundaryEncodeBHist R,
        machineInterfaceBoundaryEncodeBHist E,
        machineInterfaceBoundaryEncodeBHist F,
        machineInterfaceBoundaryEncodeBHist A,
        machineInterfaceBoundaryEncodeBHist S,
        machineInterfaceBoundaryEncodeBHist H,
        machineInterfaceBoundaryEncodeBHist C,
        machineInterfaceBoundaryEncodeBHist P,
        machineInterfaceBoundaryEncodeBHist N]

private def machineInterfaceBoundaryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => machineInterfaceBoundaryRawAt n rest

private def machineInterfaceBoundaryLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => machineInterfaceBoundaryLengthEq n rest

def machineInterfaceBoundaryFromEventFlow (ef : EventFlow) :
    Option MachineInterfaceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match machineInterfaceBoundaryLengthEq 9 ef with
  | true =>
      some
        (MachineInterfaceBoundaryUp.mk
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 0 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 1 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 2 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 3 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 4 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 5 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 6 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 7 ef))
          (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryRawAt 8 ef)))
  | false => none

private theorem machineInterfaceBoundary_round_trip :
    ∀ x : MachineInterfaceBoundaryUp,
      machineInterfaceBoundaryFromEventFlow
        (machineInterfaceBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R E F A S H C P N =>
      change
        some
          (MachineInterfaceBoundaryUp.mk
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist R))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist E))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist F))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist A))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist S))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist H))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist C))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist P))
            (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist N))) =
          some (MachineInterfaceBoundaryUp.mk R E F A S H C P N)
      rw [machineInterfaceBoundaryDecode_encode_bhist R,
        machineInterfaceBoundaryDecode_encode_bhist E,
        machineInterfaceBoundaryDecode_encode_bhist F,
        machineInterfaceBoundaryDecode_encode_bhist A,
        machineInterfaceBoundaryDecode_encode_bhist S,
        machineInterfaceBoundaryDecode_encode_bhist H,
        machineInterfaceBoundaryDecode_encode_bhist C,
        machineInterfaceBoundaryDecode_encode_bhist P,
        machineInterfaceBoundaryDecode_encode_bhist N]

private theorem machineInterfaceBoundaryToEventFlow_injective
    {x y : MachineInterfaceBoundaryUp} :
    machineInterfaceBoundaryToEventFlow x = machineInterfaceBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow x) =
        machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow y) :=
    congrArg machineInterfaceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (machineInterfaceBoundary_round_trip x).symm
      (Eq.trans hread (machineInterfaceBoundary_round_trip y)))

private theorem machineInterfaceBoundary_field_faithful :
    ∀ x y : MachineInterfaceBoundaryUp,
      machineInterfaceBoundaryFields x = machineInterfaceBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 E1 F1 A1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 E2 F2 A2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance machineInterfaceBoundaryBHistCarrier : BHistCarrier MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := machineInterfaceBoundaryToEventFlow
  fromEventFlow := machineInterfaceBoundaryFromEventFlow

instance machineInterfaceBoundaryChapterTasteGate :
    ChapterTasteGate MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow x) = some x
    exact machineInterfaceBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineInterfaceBoundaryToEventFlow_injective heq)

instance machineInterfaceBoundaryFieldFaithful :
    FieldFaithful MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := machineInterfaceBoundaryFields
  field_faithful := machineInterfaceBoundary_field_faithful

instance machineInterfaceBoundaryNontrivial : Nontrivial MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineInterfaceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MachineInterfaceBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MachineInterfaceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  machineInterfaceBoundaryChapterTasteGate

theorem MachineInterfaceBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryEncodeBHist h) = h) ∧
      (∀ x : MachineInterfaceBoundaryUp,
        machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow x) = some x) ∧
        (∀ x y : MachineInterfaceBoundaryUp,
          machineInterfaceBoundaryToEventFlow x = machineInterfaceBoundaryToEventFlow y →
            x = y) ∧
          machineInterfaceBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : MachineInterfaceBoundaryUp,
              machineInterfaceBoundaryFields x = machineInterfaceBoundaryFields y → x = y) ∧
              (∃ x y : MachineInterfaceBoundaryUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨machineInterfaceBoundaryDecode_encode_bhist,
      machineInterfaceBoundary_round_trip,
      (fun _ _ heq => machineInterfaceBoundaryToEventFlow_injective heq),
      rfl,
      machineInterfaceBoundary_field_faithful,
      by
        cases machineInterfaceBoundaryNontrivial.witness_pair with
        | mk x rest =>
            cases rest with
            | mk y hxy =>
                exact ⟨x, y, hxy⟩⟩

end BEDC.Derived.MachineInterfaceBoundaryUp
