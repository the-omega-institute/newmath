import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PerronFrobeniusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PerronFrobeniusUp : Type where
  | mk (M C I R E H T P N : BHist) : PerronFrobeniusUp
  deriving DecidableEq

def perronFrobeniusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: perronFrobeniusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: perronFrobeniusEncodeBHist h

def perronFrobeniusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (perronFrobeniusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (perronFrobeniusDecodeBHist tail)

private theorem PerronFrobeniusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def perronFrobeniusFields : PerronFrobeniusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PerronFrobeniusUp.mk M C I R E H T P N => [M, C, I, R, E, H, T, P, N]

def perronFrobeniusToEventFlow : PerronFrobeniusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (perronFrobeniusFields x).map perronFrobeniusEncodeBHist

private def perronFrobeniusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => perronFrobeniusEventAtDefault index rest

def perronFrobeniusFromEventFlow (eventFlow : EventFlow) : Option PerronFrobeniusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PerronFrobeniusUp.mk
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 0 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 1 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 2 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 3 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 4 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 5 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 6 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 7 eventFlow))
      (perronFrobeniusDecodeBHist (perronFrobeniusEventAtDefault 8 eventFlow)))

instance perronFrobeniusBHistCarrier : BHistCarrier PerronFrobeniusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := perronFrobeniusToEventFlow
  fromEventFlow := perronFrobeniusFromEventFlow

private theorem PerronFrobeniusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PerronFrobeniusUp,
      perronFrobeniusFromEventFlow (perronFrobeniusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M C I R E H T P N =>
      change
        some
            (PerronFrobeniusUp.mk
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist M))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist C))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist I))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist R))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist E))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist H))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist T))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist P))
              (perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist N))) =
          some (PerronFrobeniusUp.mk M C I R E H T P N)
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode M]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode C]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode I]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode R]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode E]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode H]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode T]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode P]
      rw [PerronFrobeniusTasteGate_single_carrier_alignment_decode N]

private theorem PerronFrobeniusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PerronFrobeniusUp} :
    perronFrobeniusToEventFlow x = perronFrobeniusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      perronFrobeniusFromEventFlow (perronFrobeniusToEventFlow x) =
        perronFrobeniusFromEventFlow (perronFrobeniusToEventFlow y) :=
    congrArg perronFrobeniusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PerronFrobeniusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PerronFrobeniusTasteGate_single_carrier_alignment_round_trip y)))

def perronFrobeniusChapterTasteGate : ChapterTasteGate PerronFrobeniusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change perronFrobeniusFromEventFlow (perronFrobeniusToEventFlow x) = some x
    exact PerronFrobeniusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PerronFrobeniusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance perronFrobeniusChapterTasteGateInstance :
    ChapterTasteGate PerronFrobeniusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  perronFrobeniusChapterTasteGate

theorem PerronFrobeniusTasteGate_single_carrier_alignment :
    (∀ h : BHist, perronFrobeniusDecodeBHist (perronFrobeniusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PerronFrobeniusUp) ∧
        Nonempty (ChapterTasteGate PerronFrobeniusUp) ∧
          perronFrobeniusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PerronFrobeniusTasteGate_single_carrier_alignment_decode,
      ⟨perronFrobeniusBHistCarrier⟩,
      ⟨perronFrobeniusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PerronFrobeniusUp
