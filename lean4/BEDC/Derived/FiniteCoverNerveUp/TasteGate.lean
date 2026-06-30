import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverNerveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverNerveUp : Type where
  | mk (K V O F R B U H C P Q : BHist) : FiniteCoverNerveUp
  deriving DecidableEq

def finiteCoverNerveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverNerveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverNerveEncodeBHist h

def finiteCoverNerveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverNerveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverNerveDecodeBHist tail)

private theorem FiniteCoverNerveTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCoverNerveFields : FiniteCoverNerveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverNerveUp.mk K V O F R B U H C P Q => [K, V, O, F, R, B, U, H, C, P, Q]

def finiteCoverNerveToEventFlow : FiniteCoverNerveUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteCoverNerveFields x).map finiteCoverNerveEncodeBHist

private def finiteCoverNerveEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCoverNerveEventAtDefault index rest

def finiteCoverNerveFromEventFlow : EventFlow → Option FiniteCoverNerveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FiniteCoverNerveUp.mk
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 0 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 1 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 2 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 3 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 4 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 5 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 6 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 7 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 8 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 9 ef))
        (finiteCoverNerveDecodeBHist (finiteCoverNerveEventAtDefault 10 ef)))

private theorem FiniteCoverNerveTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteCoverNerveUp,
      finiteCoverNerveFromEventFlow (finiteCoverNerveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K V O F R B U H C P Q =>
      change
        some
          (FiniteCoverNerveUp.mk
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist K))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist V))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist O))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist F))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist R))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist B))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist U))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist H))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist C))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist P))
            (finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist Q))) =
          some (FiniteCoverNerveUp.mk K V O F R B U H C P Q)
      rw [FiniteCoverNerveTasteGate_single_carrier_alignment_decode K,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode V,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode O,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode F,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode R,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode B,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode U,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode H,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode C,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode P,
        FiniteCoverNerveTasteGate_single_carrier_alignment_decode Q]

private theorem FiniteCoverNerveTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteCoverNerveUp} :
    finiteCoverNerveToEventFlow x = finiteCoverNerveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCoverNerveFromEventFlow (finiteCoverNerveToEventFlow x) =
        finiteCoverNerveFromEventFlow (finiteCoverNerveToEventFlow y) :=
    congrArg finiteCoverNerveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteCoverNerveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteCoverNerveTasteGate_single_carrier_alignment_round_trip y)))

instance finiteCoverNerveBHistCarrier : BHistCarrier FiniteCoverNerveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverNerveToEventFlow
  fromEventFlow := finiteCoverNerveFromEventFlow

instance finiteCoverNerveChapterTasteGate : ChapterTasteGate FiniteCoverNerveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteCoverNerveFromEventFlow (finiteCoverNerveToEventFlow x) = some x
    exact FiniteCoverNerveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteCoverNerveTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteCoverNerveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteCoverNerveChapterTasteGate

theorem FiniteCoverNerveTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteCoverNerveDecodeBHist (finiteCoverNerveEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteCoverNerveUp) ∧
        Nonempty (ChapterTasteGate FiniteCoverNerveUp) ∧
          finiteCoverNerveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteCoverNerveTasteGate_single_carrier_alignment_decode,
      ⟨finiteCoverNerveBHistCarrier⟩,
      ⟨finiteCoverNerveChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteCoverNerveUp
