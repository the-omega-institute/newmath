import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirichletKernelUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirichletKernelUp : Type where
  | mk (W A S Z F R H C P N : BHist) : DirichletKernelUp
  deriving DecidableEq

def dirichletKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dirichletKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dirichletKernelEncodeBHist h

def dirichletKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dirichletKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dirichletKernelDecodeBHist tail)

private theorem dirichletKernelDecodeEncodeBHist :
    ∀ h : BHist, dirichletKernelDecodeBHist (dirichletKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dirichletKernelFields : DirichletKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletKernelUp.mk W A S Z F R H C P N => [W, A, S, Z, F, R, H, C, P, N]

def dirichletKernelToEventFlow : DirichletKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map dirichletKernelEncodeBHist (dirichletKernelFields x)

private def dirichletKernelEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dirichletKernelEventAt index rest

def dirichletKernelFromEventFlow : EventFlow → Option DirichletKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DirichletKernelUp.mk
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 0 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 1 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 2 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 3 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 4 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 5 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 6 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 7 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 8 ef))
          (dirichletKernelDecodeBHist (dirichletKernelEventAt 9 ef)))

private theorem dirichletKernelRoundTrip :
    ∀ x : DirichletKernelUp,
      dirichletKernelFromEventFlow (dirichletKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W A S Z F R H C P N =>
      change
        some
          (DirichletKernelUp.mk
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist W))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist A))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist S))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist Z))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist F))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist R))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist H))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist C))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist P))
            (dirichletKernelDecodeBHist (dirichletKernelEncodeBHist N))) =
          some (DirichletKernelUp.mk W A S Z F R H C P N)
      rw [dirichletKernelDecodeEncodeBHist W, dirichletKernelDecodeEncodeBHist A,
        dirichletKernelDecodeEncodeBHist S, dirichletKernelDecodeEncodeBHist Z,
        dirichletKernelDecodeEncodeBHist F, dirichletKernelDecodeEncodeBHist R,
        dirichletKernelDecodeEncodeBHist H, dirichletKernelDecodeEncodeBHist C,
        dirichletKernelDecodeEncodeBHist P, dirichletKernelDecodeEncodeBHist N]

private theorem dirichletKernelToEventFlow_injective {x y : DirichletKernelUp} :
    dirichletKernelToEventFlow x = dirichletKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dirichletKernelFromEventFlow (dirichletKernelToEventFlow x) =
        dirichletKernelFromEventFlow (dirichletKernelToEventFlow y) :=
    congrArg dirichletKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dirichletKernelRoundTrip x).symm
      (Eq.trans hread (dirichletKernelRoundTrip y)))

instance dirichletKernelBHistCarrier : BHistCarrier DirichletKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dirichletKernelToEventFlow
  fromEventFlow := dirichletKernelFromEventFlow

instance dirichletKernelChapterTasteGate : ChapterTasteGate DirichletKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dirichletKernelFromEventFlow (dirichletKernelToEventFlow x) = some x
    exact dirichletKernelRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dirichletKernelToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DirichletKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dirichletKernelChapterTasteGate

theorem DirichletKernelTasteGate_single_carrier_alignment :
    (∀ h : BHist, dirichletKernelDecodeBHist (dirichletKernelEncodeBHist h) = h) ∧
      (∀ x : DirichletKernelUp,
        dirichletKernelFromEventFlow (dirichletKernelToEventFlow x) = some x) ∧
        (∀ x y : DirichletKernelUp,
          dirichletKernelToEventFlow x = dirichletKernelToEventFlow y → x = y) ∧
          dirichletKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dirichletKernelDecodeEncodeBHist,
      dirichletKernelRoundTrip,
      (fun _ _ heq => dirichletKernelToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DirichletKernelUp.TasteGate
