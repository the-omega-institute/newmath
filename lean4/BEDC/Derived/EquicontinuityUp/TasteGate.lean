import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuityUp : Type where
  | mk (K F eps rho M T R P N : BHist) : EquicontinuityUp
  deriving DecidableEq

def equicontinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuityEncodeBHist h

def equicontinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuityDecodeBHist tail)

private theorem EquicontinuityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, equicontinuityDecodeBHist (equicontinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuityFields : EquicontinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuityUp.mk K F eps rho M T R P N => [K, F, eps, rho, M, T, R, P, N]

def equicontinuityToEventFlow : EquicontinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (equicontinuityFields x).map equicontinuityEncodeBHist

private def equicontinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => equicontinuityEventAtDefault index rest

def equicontinuityFromEventFlow (ef : EventFlow) : Option EquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EquicontinuityUp.mk
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 0 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 1 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 2 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 3 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 4 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 5 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 6 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 7 ef))
      (equicontinuityDecodeBHist (equicontinuityEventAtDefault 8 ef)))

private theorem EquicontinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EquicontinuityUp,
      equicontinuityFromEventFlow (equicontinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F eps rho M T R P N =>
      change
        some
          (EquicontinuityUp.mk
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist K))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist F))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist eps))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist rho))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist M))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist T))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist R))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist P))
            (equicontinuityDecodeBHist (equicontinuityEncodeBHist N))) =
          some (EquicontinuityUp.mk K F eps rho M T R P N)
      rw [EquicontinuityTasteGate_single_carrier_alignment_decode K,
        EquicontinuityTasteGate_single_carrier_alignment_decode F,
        EquicontinuityTasteGate_single_carrier_alignment_decode eps,
        EquicontinuityTasteGate_single_carrier_alignment_decode rho,
        EquicontinuityTasteGate_single_carrier_alignment_decode M,
        EquicontinuityTasteGate_single_carrier_alignment_decode T,
        EquicontinuityTasteGate_single_carrier_alignment_decode R,
        EquicontinuityTasteGate_single_carrier_alignment_decode P,
        EquicontinuityTasteGate_single_carrier_alignment_decode N]

private theorem EquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EquicontinuityUp} :
    equicontinuityToEventFlow x = equicontinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuityFromEventFlow (equicontinuityToEventFlow x) =
        equicontinuityFromEventFlow (equicontinuityToEventFlow y) :=
    congrArg equicontinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EquicontinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EquicontinuityTasteGate_single_carrier_alignment_round_trip y)))

instance equicontinuityBHistCarrier : BHistCarrier EquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuityToEventFlow
  fromEventFlow := equicontinuityFromEventFlow

instance equicontinuityChapterTasteGate : ChapterTasteGate EquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change equicontinuityFromEventFlow (equicontinuityToEventFlow x) = some x
    exact EquicontinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem EquicontinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist, equicontinuityDecodeBHist (equicontinuityEncodeBHist h) = h) ∧
      (∀ x : EquicontinuityUp,
        equicontinuityFromEventFlow (equicontinuityToEventFlow x) = some x) ∧
        (∀ x y : EquicontinuityUp,
          equicontinuityToEventFlow x = equicontinuityToEventFlow y → x = y) ∧
          equicontinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨EquicontinuityTasteGate_single_carrier_alignment_decode,
      EquicontinuityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        EquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EquicontinuityUp
