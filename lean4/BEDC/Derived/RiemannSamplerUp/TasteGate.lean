import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannSamplerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannSamplerUp : Type where
  | mk (D R P T F V H C G N : BHist) : RiemannSamplerUp
  deriving DecidableEq

def riemannSamplerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannSamplerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannSamplerEncodeBHist h

def riemannSamplerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannSamplerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannSamplerDecodeBHist tail)

private theorem RiemannSamplerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, riemannSamplerDecodeBHist (riemannSamplerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannSamplerFields : RiemannSamplerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannSamplerUp.mk D R P T F V H C G N => [D, R, P, T, F, V, H, C, G, N]

def riemannSamplerToEventFlow : RiemannSamplerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannSamplerFields x).map riemannSamplerEncodeBHist

private def riemannSamplerEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannSamplerEventAt index rest

def riemannSamplerFromEventFlow : EventFlow → Option RiemannSamplerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    some
      (RiemannSamplerUp.mk
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 0 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 1 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 2 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 3 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 4 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 5 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 6 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 7 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 8 eventFlow))
        (riemannSamplerDecodeBHist (riemannSamplerEventAt 9 eventFlow)))

private theorem RiemannSamplerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannSamplerUp,
      riemannSamplerFromEventFlow (riemannSamplerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D R P T F V H C G N =>
      change
        some
            (RiemannSamplerUp.mk
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist D))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist R))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist P))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist T))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist F))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist V))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist H))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist C))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist G))
              (riemannSamplerDecodeBHist (riemannSamplerEncodeBHist N))) =
          some (RiemannSamplerUp.mk D R P T F V H C G N)
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode D]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode R]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode P]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode T]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode F]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode V]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode H]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode C]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode G]
      rw [RiemannSamplerTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannSamplerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannSamplerUp} :
    riemannSamplerToEventFlow x = riemannSamplerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannSamplerFromEventFlow (riemannSamplerToEventFlow x) =
        riemannSamplerFromEventFlow (riemannSamplerToEventFlow y) :=
    congrArg riemannSamplerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannSamplerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RiemannSamplerTasteGate_single_carrier_alignment_round_trip y)))

instance riemannSamplerBHistCarrier : BHistCarrier RiemannSamplerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannSamplerToEventFlow
  fromEventFlow := riemannSamplerFromEventFlow

instance riemannSamplerChapterTasteGate : ChapterTasteGate RiemannSamplerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannSamplerFromEventFlow (riemannSamplerToEventFlow x) = some x
    exact RiemannSamplerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannSamplerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RiemannSamplerTasteGate_single_carrier_alignment :
    (∀ h : BHist, riemannSamplerDecodeBHist (riemannSamplerEncodeBHist h) = h) ∧
      (∀ x : RiemannSamplerUp,
        riemannSamplerFromEventFlow (riemannSamplerToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier RiemannSamplerUp) ∧
        Nonempty (ChapterTasteGate RiemannSamplerUp) ∧
          riemannSamplerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RiemannSamplerTasteGate_single_carrier_alignment_decode_encode,
      RiemannSamplerTasteGate_single_carrier_alignment_round_trip,
      ⟨riemannSamplerBHistCarrier⟩, ⟨riemannSamplerChapterTasteGate⟩, rfl⟩

end BEDC.Derived.RiemannSamplerUp
