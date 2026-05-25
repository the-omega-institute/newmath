import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusSelectionUp : Type where
  | mk (R D W M T E H C P N : BHist) : CauchyModulusSelectionUp
  deriving DecidableEq

def cauchyModulusSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusSelectionEncodeBHist h

def cauchyModulusSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusSelectionDecodeBHist tail)

private theorem CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusSelectionFields : CauchyModulusSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusSelectionUp.mk R D W M T E H C P N => [R, D, W, M, T, E, H, C, P, N]

def cauchyModulusSelectionToEventFlow : CauchyModulusSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusSelectionFields x).map cauchyModulusSelectionEncodeBHist

private def cauchyModulusSelectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusSelectionEventAt index rest

def cauchyModulusSelectionFromEventFlow (ef : EventFlow) :
    Option CauchyModulusSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusSelectionUp.mk
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 0 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 1 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 2 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 3 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 4 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 5 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 6 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 7 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 8 ef))
      (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEventAt 9 ef)))

private theorem CauchyModulusSelectionTasteGate_single_carrier_alignment_round_trip
    (x : CauchyModulusSelectionUp) :
    cauchyModulusSelectionFromEventFlow (cauchyModulusSelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R D W M T E H C P N =>
      change
        some
          (CauchyModulusSelectionUp.mk
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist R))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist D))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist W))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist M))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist T))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist E))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist H))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist C))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist P))
            (cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist N))) =
          some (CauchyModulusSelectionUp.mk R D W M T E H C P N)
      rw [CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode W,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode M,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode T,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyModulusSelectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusSelectionUp} :
    cauchyModulusSelectionToEventFlow x = cauchyModulusSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusSelectionFromEventFlow (cauchyModulusSelectionToEventFlow x) =
        cauchyModulusSelectionFromEventFlow (cauchyModulusSelectionToEventFlow y) :=
    congrArg cauchyModulusSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyModulusSelectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusSelectionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyModulusSelectionBHistCarrier : BHistCarrier CauchyModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusSelectionToEventFlow
  fromEventFlow := cauchyModulusSelectionFromEventFlow

instance cauchyModulusSelectionChapterTasteGate :
    ChapterTasteGate CauchyModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusSelectionFromEventFlow (cauchyModulusSelectionToEventFlow x) =
      some x
    exact CauchyModulusSelectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyModulusSelectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyModulusSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyModulusSelectionDecodeBHist (cauchyModulusSelectionEncodeBHist h) = h) ∧
      (∀ x : CauchyModulusSelectionUp,
        cauchyModulusSelectionFromEventFlow (cauchyModulusSelectionToEventFlow x) = some x) ∧
        (∀ x y : CauchyModulusSelectionUp,
          cauchyModulusSelectionToEventFlow x = cauchyModulusSelectionToEventFlow y → x = y) ∧
          cauchyModulusSelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyModulusSelectionTasteGate_single_carrier_alignment_decode_encode,
      CauchyModulusSelectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyModulusSelectionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyModulusSelectionUp
