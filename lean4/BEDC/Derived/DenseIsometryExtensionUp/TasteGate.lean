import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenseIsometryExtensionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenseIsometryExtensionUp : Type where
  | mk (D J U S F W T R H C P N : BHist) : DenseIsometryExtensionUp
  deriving DecidableEq

def denseIsometryExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denseIsometryExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denseIsometryExtensionEncodeBHist h

def denseIsometryExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denseIsometryExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denseIsometryExtensionDecodeBHist tail)

private theorem DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def denseIsometryExtensionFields : DenseIsometryExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenseIsometryExtensionUp.mk D J U S F W T R H C P N =>
      [D, J, U, S, F, W, T, R, H, C, P, N]

def denseIsometryExtensionToEventFlow : DenseIsometryExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (denseIsometryExtensionFields x).map denseIsometryExtensionEncodeBHist

private def denseIsometryExtensionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => denseIsometryExtensionEventAt index rest

def denseIsometryExtensionFromEventFlow (ef : EventFlow) : Option DenseIsometryExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenseIsometryExtensionUp.mk
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 0 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 1 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 2 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 3 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 4 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 5 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 6 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 7 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 8 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 9 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 10 ef))
      (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEventAt 11 ef)))

private theorem DenseIsometryExtensionTasteGate_single_carrier_alignment_round_trip
    (x : DenseIsometryExtensionUp) :
    denseIsometryExtensionFromEventFlow (denseIsometryExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D J U S F W T R H C P N =>
      change
        some
          (DenseIsometryExtensionUp.mk
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist D))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist J))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist U))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist S))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist F))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist W))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist T))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist R))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist H))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist C))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist P))
            (denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist N))) =
          some (DenseIsometryExtensionUp.mk D J U S F W T R H C P N)
      rw [DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode D,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode J,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode U,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode S,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode F,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode W,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode T,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode R,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode H,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode C,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode P,
        DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DenseIsometryExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DenseIsometryExtensionUp} :
    denseIsometryExtensionToEventFlow x = denseIsometryExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denseIsometryExtensionFromEventFlow (denseIsometryExtensionToEventFlow x) =
        denseIsometryExtensionFromEventFlow (denseIsometryExtensionToEventFlow y) :=
    congrArg denseIsometryExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DenseIsometryExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DenseIsometryExtensionTasteGate_single_carrier_alignment_round_trip y)))

instance denseIsometryExtensionBHistCarrier : BHistCarrier DenseIsometryExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denseIsometryExtensionToEventFlow
  fromEventFlow := denseIsometryExtensionFromEventFlow

instance denseIsometryExtensionChapterTasteGate : ChapterTasteGate DenseIsometryExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change denseIsometryExtensionFromEventFlow (denseIsometryExtensionToEventFlow x) = some x
    exact DenseIsometryExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DenseIsometryExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def DenseIsometryExtensionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DenseIsometryExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  denseIsometryExtensionChapterTasteGate

theorem DenseIsometryExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      denseIsometryExtensionDecodeBHist (denseIsometryExtensionEncodeBHist h) = h) ∧
      (∀ x : DenseIsometryExtensionUp,
        denseIsometryExtensionFromEventFlow (denseIsometryExtensionToEventFlow x) = some x) ∧
        (∀ x y : DenseIsometryExtensionUp,
          denseIsometryExtensionToEventFlow x = denseIsometryExtensionToEventFlow y → x = y) ∧
          denseIsometryExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DenseIsometryExtensionTasteGate_single_carrier_alignment_decode_encode,
      DenseIsometryExtensionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DenseIsometryExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DenseIsometryExtensionUp.TasteGate
