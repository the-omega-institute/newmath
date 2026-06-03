import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LaplaceTransformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LaplaceTransformUp : Type where
  | mk (K I F W O H C P N : BHist) : LaplaceTransformUp
  deriving DecidableEq

def laplaceTransformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: laplaceTransformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: laplaceTransformEncodeBHist h

def laplaceTransformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (laplaceTransformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (laplaceTransformDecodeBHist tail)

private theorem LaplaceTransformTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, laplaceTransformDecodeBHist (laplaceTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def laplaceTransformToEventFlow : LaplaceTransformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LaplaceTransformUp.mk K I F W O H C P N =>
      [laplaceTransformEncodeBHist K,
        laplaceTransformEncodeBHist I,
        laplaceTransformEncodeBHist F,
        laplaceTransformEncodeBHist W,
        laplaceTransformEncodeBHist O,
        laplaceTransformEncodeBHist H,
        laplaceTransformEncodeBHist C,
        laplaceTransformEncodeBHist P,
        laplaceTransformEncodeBHist N]

private def laplaceTransformEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => laplaceTransformEventAtDefault index rest

def laplaceTransformFromEventFlow (ef : EventFlow) : Option LaplaceTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LaplaceTransformUp.mk
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 0 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 1 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 2 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 3 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 4 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 5 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 6 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 7 ef))
      (laplaceTransformDecodeBHist (laplaceTransformEventAtDefault 8 ef)))

private theorem LaplaceTransformTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LaplaceTransformUp,
      laplaceTransformFromEventFlow (laplaceTransformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K I F W O H C P N =>
      change
        some
            (LaplaceTransformUp.mk
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist K))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist I))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist F))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist W))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist O))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist H))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist C))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist P))
              (laplaceTransformDecodeBHist (laplaceTransformEncodeBHist N))) =
          some (LaplaceTransformUp.mk K I F W O H C P N)
      rw [LaplaceTransformTasteGate_single_carrier_alignment_decode K,
        LaplaceTransformTasteGate_single_carrier_alignment_decode I,
        LaplaceTransformTasteGate_single_carrier_alignment_decode F,
        LaplaceTransformTasteGate_single_carrier_alignment_decode W,
        LaplaceTransformTasteGate_single_carrier_alignment_decode O,
        LaplaceTransformTasteGate_single_carrier_alignment_decode H,
        LaplaceTransformTasteGate_single_carrier_alignment_decode C,
        LaplaceTransformTasteGate_single_carrier_alignment_decode P,
        LaplaceTransformTasteGate_single_carrier_alignment_decode N]

private theorem laplaceTransformToEventFlow_injective {x y : LaplaceTransformUp} :
    laplaceTransformToEventFlow x = laplaceTransformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      laplaceTransformFromEventFlow (laplaceTransformToEventFlow x) =
        laplaceTransformFromEventFlow (laplaceTransformToEventFlow y) :=
    congrArg laplaceTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LaplaceTransformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LaplaceTransformTasteGate_single_carrier_alignment_round_trip y)))

instance laplaceTransformBHistCarrier : BHistCarrier LaplaceTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := laplaceTransformToEventFlow
  fromEventFlow := laplaceTransformFromEventFlow

instance laplaceTransformChapterTasteGate : ChapterTasteGate LaplaceTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change laplaceTransformFromEventFlow (laplaceTransformToEventFlow x) = some x
    exact LaplaceTransformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (laplaceTransformToEventFlow_injective heq)

theorem LaplaceTransformTasteGate_single_carrier_alignment :
    (∀ h : BHist, laplaceTransformDecodeBHist (laplaceTransformEncodeBHist h) = h) ∧
      (∀ x : LaplaceTransformUp,
        laplaceTransformFromEventFlow (laplaceTransformToEventFlow x) = some x) ∧
        (∀ x y : LaplaceTransformUp,
          laplaceTransformToEventFlow x = laplaceTransformToEventFlow y → x = y) ∧
          laplaceTransformEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LaplaceTransformTasteGate_single_carrier_alignment_decode,
      LaplaceTransformTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => laplaceTransformToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LaplaceTransformUp
