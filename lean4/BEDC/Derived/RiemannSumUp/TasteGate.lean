import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannSumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannSumUp : Type where
  | mk (M T F W S H C P N : BHist) : RiemannSumUp
  deriving DecidableEq

def riemannSumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannSumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannSumEncodeBHist h

def riemannSumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannSumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannSumDecodeBHist tail)

private theorem RiemannSumTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, riemannSumDecodeBHist (riemannSumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannSumFields : RiemannSumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannSumUp.mk M T F W S H C P N => [M, T, F, W, S, H, C, P, N]

def riemannSumToEventFlow : RiemannSumUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (riemannSumFields x).map riemannSumEncodeBHist

private def riemannSumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannSumEventAtDefault index rest

def riemannSumFromEventFlow (ef : EventFlow) : Option RiemannSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannSumUp.mk
      (riemannSumDecodeBHist (riemannSumEventAtDefault 0 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 1 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 2 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 3 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 4 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 5 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 6 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 7 ef))
      (riemannSumDecodeBHist (riemannSumEventAtDefault 8 ef)))

private theorem RiemannSumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannSumUp, riemannSumFromEventFlow (riemannSumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T F W S H C P N =>
      change
        some
          (RiemannSumUp.mk
            (riemannSumDecodeBHist (riemannSumEncodeBHist M))
            (riemannSumDecodeBHist (riemannSumEncodeBHist T))
            (riemannSumDecodeBHist (riemannSumEncodeBHist F))
            (riemannSumDecodeBHist (riemannSumEncodeBHist W))
            (riemannSumDecodeBHist (riemannSumEncodeBHist S))
            (riemannSumDecodeBHist (riemannSumEncodeBHist H))
            (riemannSumDecodeBHist (riemannSumEncodeBHist C))
            (riemannSumDecodeBHist (riemannSumEncodeBHist P))
            (riemannSumDecodeBHist (riemannSumEncodeBHist N))) =
          some (RiemannSumUp.mk M T F W S H C P N)
      rw [RiemannSumTasteGate_single_carrier_alignment_decode M,
        RiemannSumTasteGate_single_carrier_alignment_decode T,
        RiemannSumTasteGate_single_carrier_alignment_decode F,
        RiemannSumTasteGate_single_carrier_alignment_decode W,
        RiemannSumTasteGate_single_carrier_alignment_decode S,
        RiemannSumTasteGate_single_carrier_alignment_decode H,
        RiemannSumTasteGate_single_carrier_alignment_decode C,
        RiemannSumTasteGate_single_carrier_alignment_decode P,
        RiemannSumTasteGate_single_carrier_alignment_decode N]

private theorem RiemannSumTasteGate_single_carrier_alignment_injective
    {x y : RiemannSumUp} :
    riemannSumToEventFlow x = riemannSumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannSumFromEventFlow (riemannSumToEventFlow x) =
        riemannSumFromEventFlow (riemannSumToEventFlow y) :=
    congrArg riemannSumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RiemannSumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RiemannSumTasteGate_single_carrier_alignment_round_trip y)))

instance riemannSumBHistCarrier : BHistCarrier RiemannSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannSumToEventFlow
  fromEventFlow := riemannSumFromEventFlow

instance riemannSumChapterTasteGate : ChapterTasteGate RiemannSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannSumFromEventFlow (riemannSumToEventFlow x) = some x
    exact RiemannSumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannSumTasteGate_single_carrier_alignment_injective heq)

theorem RiemannSumTasteGate_single_carrier_alignment :
    (∀ h : BHist, riemannSumDecodeBHist (riemannSumEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RiemannSumUp) ∧
        Nonempty (ChapterTasteGate RiemannSumUp) ∧
          riemannSumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RiemannSumTasteGate_single_carrier_alignment_decode,
      ⟨⟨riemannSumBHistCarrier⟩, ⟨riemannSumChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.RiemannSumUp
