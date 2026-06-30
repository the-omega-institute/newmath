import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareDiskGeodesicProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareDiskGeodesicProjectionUp : Type where
  | mk (D B M T J H C P N : BHist) : PoincareDiskGeodesicProjectionUp
  deriving DecidableEq

def poincareDiskGeodesicProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareDiskGeodesicProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareDiskGeodesicProjectionEncodeBHist h

def poincareDiskGeodesicProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareDiskGeodesicProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareDiskGeodesicProjectionDecodeBHist tail)

private theorem PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def poincareDiskGeodesicProjectionFields :
    PoincareDiskGeodesicProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareDiskGeodesicProjectionUp.mk D B M T J H C P N =>
      [D, B, M, T, J, H, C, P, N]

def poincareDiskGeodesicProjectionToEventFlow :
    PoincareDiskGeodesicProjectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (poincareDiskGeodesicProjectionFields x).map
        poincareDiskGeodesicProjectionEncodeBHist

private def poincareDiskGeodesicProjectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => poincareDiskGeodesicProjectionEventAt index rest

def poincareDiskGeodesicProjectionFromEventFlow
    (eventFlow : EventFlow) : Option PoincareDiskGeodesicProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PoincareDiskGeodesicProjectionUp.mk
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 0 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 1 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 2 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 3 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 4 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 5 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 6 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 7 eventFlow))
      (poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEventAt 8 eventFlow)))

private theorem PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PoincareDiskGeodesicProjectionUp,
      poincareDiskGeodesicProjectionFromEventFlow
        (poincareDiskGeodesicProjectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D B M T J H C P N =>
      change
        some
            (PoincareDiskGeodesicProjectionUp.mk
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist D))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist B))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist M))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist T))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist J))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist H))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist C))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist P))
              (poincareDiskGeodesicProjectionDecodeBHist
                (poincareDiskGeodesicProjectionEncodeBHist N))) =
          some (PoincareDiskGeodesicProjectionUp.mk D B M T J H C P N)
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode D]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode B]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode M]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode T]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode J]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode H]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode C]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode P]
      rw [PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PoincareDiskGeodesicProjectionUp} :
    poincareDiskGeodesicProjectionToEventFlow x =
        poincareDiskGeodesicProjectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareDiskGeodesicProjectionFromEventFlow
          (poincareDiskGeodesicProjectionToEventFlow x) =
        poincareDiskGeodesicProjectionFromEventFlow
          (poincareDiskGeodesicProjectionToEventFlow y) :=
    congrArg poincareDiskGeodesicProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_round_trip y)))

instance poincareDiskGeodesicProjectionBHistCarrier :
    BHistCarrier PoincareDiskGeodesicProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareDiskGeodesicProjectionToEventFlow
  fromEventFlow := poincareDiskGeodesicProjectionFromEventFlow

instance poincareDiskGeodesicProjectionChapterTasteGate :
    ChapterTasteGate PoincareDiskGeodesicProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      poincareDiskGeodesicProjectionFromEventFlow
        (poincareDiskGeodesicProjectionToEventFlow x) = some x
    exact PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate PoincareDiskGeodesicProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  poincareDiskGeodesicProjectionChapterTasteGate

theorem PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      poincareDiskGeodesicProjectionDecodeBHist
        (poincareDiskGeodesicProjectionEncodeBHist h) = h) ∧
      (∀ x : PoincareDiskGeodesicProjectionUp,
        poincareDiskGeodesicProjectionFromEventFlow
          (poincareDiskGeodesicProjectionToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier PoincareDiskGeodesicProjectionUp) ∧
      Nonempty (ChapterTasteGate PoincareDiskGeodesicProjectionUp) ∧
      poincareDiskGeodesicProjectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_decode_encode,
      PoincareDiskGeodesicProjectionTasteGate_single_carrier_alignment_round_trip,
      ⟨poincareDiskGeodesicProjectionBHistCarrier⟩,
      ⟨poincareDiskGeodesicProjectionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.PoincareDiskGeodesicProjectionUp
