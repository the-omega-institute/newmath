import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiracPointMassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiracPointMassUp : Type where
  | mk (X p E U D H C P N : BHist) : DiracPointMassUp
  deriving DecidableEq

def diracPointMassEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diracPointMassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diracPointMassEncodeBHist h

def diracPointMassDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diracPointMassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diracPointMassDecodeBHist tail)

private theorem DiracPointMassTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, diracPointMassDecodeBHist (diracPointMassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diracPointMassFields : DiracPointMassUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiracPointMassUp.mk X p E U D H C P N => [X, p, E, U, D, H, C, P, N]

def diracPointMassToEventFlow : DiracPointMassUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diracPointMassFields x).map diracPointMassEncodeBHist

private def diracPointMassEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diracPointMassEventAtDefault index rest

def diracPointMassFromEventFlow (ef : EventFlow) : Option DiracPointMassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiracPointMassUp.mk
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 0 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 1 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 2 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 3 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 4 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 5 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 6 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 7 ef))
      (diracPointMassDecodeBHist (diracPointMassEventAtDefault 8 ef)))

private theorem DiracPointMassTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiracPointMassUp, diracPointMassFromEventFlow (diracPointMassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X p E U D H C P N =>
      change
        some
          (DiracPointMassUp.mk
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist X))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist p))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist E))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist U))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist D))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist H))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist C))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist P))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist N))) =
          some (DiracPointMassUp.mk X p E U D H C P N)
      rw [DiracPointMassTasteGate_single_carrier_alignment_decode X,
        DiracPointMassTasteGate_single_carrier_alignment_decode p,
        DiracPointMassTasteGate_single_carrier_alignment_decode E,
        DiracPointMassTasteGate_single_carrier_alignment_decode U,
        DiracPointMassTasteGate_single_carrier_alignment_decode D,
        DiracPointMassTasteGate_single_carrier_alignment_decode H,
        DiracPointMassTasteGate_single_carrier_alignment_decode C,
        DiracPointMassTasteGate_single_carrier_alignment_decode P,
        DiracPointMassTasteGate_single_carrier_alignment_decode N]

private theorem DiracPointMassTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiracPointMassUp} :
    diracPointMassToEventFlow x = diracPointMassToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diracPointMassFromEventFlow (diracPointMassToEventFlow x) =
        diracPointMassFromEventFlow (diracPointMassToEventFlow y) :=
    congrArg diracPointMassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiracPointMassTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiracPointMassTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiracPointMassTasteGate_single_carrier_alignment_fields :
    ∀ x y : DiracPointMassUp, diracPointMassFields x = diracPointMassFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 p1 E1 U1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 p2 E2 U2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance diracPointMassBHistCarrier : BHistCarrier DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diracPointMassToEventFlow
  fromEventFlow := diracPointMassFromEventFlow

instance diracPointMassChapterTasteGate : ChapterTasteGate DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diracPointMassFromEventFlow (diracPointMassToEventFlow x) = some x
    exact DiracPointMassTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiracPointMassTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance diracPointMassFieldFaithful : FieldFaithful DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diracPointMassFields
  field_faithful := DiracPointMassTasteGate_single_carrier_alignment_fields

instance diracPointMassNontrivial : BEDC.Meta.TasteGate.Nontrivial DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiracPointMassUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiracPointMassUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiracPointMassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diracPointMassChapterTasteGate

theorem DiracPointMassTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DiracPointMassUp) ∧
      Nonempty (FieldFaithful DiracPointMassUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DiracPointMassUp) ∧
          (∀ h : BHist, diracPointMassDecodeBHist (diracPointMassEncodeBHist h) = h) ∧
            (∀ x : DiracPointMassUp,
              diracPointMassFromEventFlow (diracPointMassToEventFlow x) = some x) ∧
              (∀ x y : DiracPointMassUp,
                diracPointMassToEventFlow x = diracPointMassToEventFlow y → x = y) ∧
                diracPointMassEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨diracPointMassChapterTasteGate⟩,
      ⟨diracPointMassFieldFaithful⟩,
      ⟨diracPointMassNontrivial⟩,
      DiracPointMassTasteGate_single_carrier_alignment_decode,
      DiracPointMassTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DiracPointMassTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DiracPointMassUp
