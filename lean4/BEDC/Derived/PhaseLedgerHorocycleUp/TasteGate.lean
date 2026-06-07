import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhaseLedgerHorocycleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhaseLedgerHorocycleUp : Type where
  | mk (F D M Q T Y H C P N : BHist) : PhaseLedgerHorocycleUp
  deriving DecidableEq

def phaseLedgerHorocycleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: phaseLedgerHorocycleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: phaseLedgerHorocycleEncodeBHist h

def phaseLedgerHorocycleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (phaseLedgerHorocycleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (phaseLedgerHorocycleDecodeBHist tail)

private theorem phaseLedgerHorocycle_decode_encode :
    ∀ h : BHist,
      phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def phaseLedgerHorocycleFields : PhaseLedgerHorocycleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhaseLedgerHorocycleUp.mk F D M Q T Y H C P N => [F, D, M, Q, T, Y, H, C, P, N]

def phaseLedgerHorocycleToEventFlow : PhaseLedgerHorocycleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (phaseLedgerHorocycleFields x).map phaseLedgerHorocycleEncodeBHist

private def phaseLedgerHorocycleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => phaseLedgerHorocycleEventAtDefault index rest

def phaseLedgerHorocycleFromEventFlow
    (ef : EventFlow) : Option PhaseLedgerHorocycleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhaseLedgerHorocycleUp.mk
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 0 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 1 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 2 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 3 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 4 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 5 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 6 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 7 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 8 ef))
      (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEventAtDefault 9 ef)))

private theorem phaseLedgerHorocycle_round_trip (x : PhaseLedgerHorocycleUp) :
    phaseLedgerHorocycleFromEventFlow (phaseLedgerHorocycleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F D M Q T Y H C P N =>
      change
        some
          (PhaseLedgerHorocycleUp.mk
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist F))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist D))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist M))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist Q))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist T))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist Y))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist H))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist C))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist P))
            (phaseLedgerHorocycleDecodeBHist (phaseLedgerHorocycleEncodeBHist N))) =
          some (PhaseLedgerHorocycleUp.mk F D M Q T Y H C P N)
      rw [phaseLedgerHorocycle_decode_encode F, phaseLedgerHorocycle_decode_encode D,
        phaseLedgerHorocycle_decode_encode M, phaseLedgerHorocycle_decode_encode Q,
        phaseLedgerHorocycle_decode_encode T, phaseLedgerHorocycle_decode_encode Y,
        phaseLedgerHorocycle_decode_encode H, phaseLedgerHorocycle_decode_encode C,
        phaseLedgerHorocycle_decode_encode P, phaseLedgerHorocycle_decode_encode N]

private theorem phaseLedgerHorocycleToEventFlow_injective
    {x y : PhaseLedgerHorocycleUp} :
    phaseLedgerHorocycleToEventFlow x = phaseLedgerHorocycleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      phaseLedgerHorocycleFromEventFlow (phaseLedgerHorocycleToEventFlow x) =
        phaseLedgerHorocycleFromEventFlow (phaseLedgerHorocycleToEventFlow y) :=
    congrArg phaseLedgerHorocycleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (phaseLedgerHorocycle_round_trip x).symm
      (Eq.trans hread (phaseLedgerHorocycle_round_trip y)))

private theorem phaseLedgerHorocycle_fields_faithful :
    ∀ x y : PhaseLedgerHorocycleUp,
      phaseLedgerHorocycleFields x = phaseLedgerHorocycleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 D1 M1 Q1 T1 Y1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 D2 M2 Q2 T2 Y2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance phaseLedgerHorocycleBHistCarrier : BHistCarrier PhaseLedgerHorocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := phaseLedgerHorocycleToEventFlow
  fromEventFlow := phaseLedgerHorocycleFromEventFlow

instance phaseLedgerHorocycleChapterTasteGate : ChapterTasteGate PhaseLedgerHorocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change phaseLedgerHorocycleFromEventFlow (phaseLedgerHorocycleToEventFlow x) = some x
    exact phaseLedgerHorocycle_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (phaseLedgerHorocycleToEventFlow_injective heq)

instance phaseLedgerHorocycleFieldFaithful : FieldFaithful PhaseLedgerHorocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := phaseLedgerHorocycleFields
  field_faithful := phaseLedgerHorocycle_fields_faithful

instance phaseLedgerHorocycleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PhaseLedgerHorocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhaseLedgerHorocycleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhaseLedgerHorocycleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhaseLedgerHorocycleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  phaseLedgerHorocycleChapterTasteGate

theorem PhaseLedgerHorocycleTasteGate_single_carrier_alignment :
    phaseLedgerHorocycleFromEventFlow
        (phaseLedgerHorocycleToEventFlow
          (PhaseLedgerHorocycleUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty)) =
      some
        (PhaseLedgerHorocycleUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty) ∧
      Nonempty (FieldFaithful PhaseLedgerHorocycleUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial PhaseLedgerHorocycleUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨phaseLedgerHorocycle_round_trip
      (PhaseLedgerHorocycleUp.mk BHist.Empty (BHist.e0 BHist.Empty)
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty),
      Nonempty.intro phaseLedgerHorocycleFieldFaithful,
      Nonempty.intro phaseLedgerHorocycleNontrivial⟩

end BEDC.Derived.PhaseLedgerHorocycleUp
