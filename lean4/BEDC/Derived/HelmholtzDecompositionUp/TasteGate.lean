import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HelmholtzDecompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HelmholtzDecompositionUp : Type where
  | mk (H V G D O B T C P N : BHist) : HelmholtzDecompositionUp
  deriving DecidableEq

def helmholtzDecompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: helmholtzDecompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: helmholtzDecompositionEncodeBHist h

def helmholtzDecompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (helmholtzDecompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (helmholtzDecompositionDecodeBHist tail)

private theorem HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def helmholtzDecompositionFields : HelmholtzDecompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HelmholtzDecompositionUp.mk H V G D O B T C P N => [H, V, G, D, O, B, T, C, P, N]

def helmholtzDecompositionToEventFlow : HelmholtzDecompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (helmholtzDecompositionFields x).map helmholtzDecompositionEncodeBHist

private def HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt index rest

def helmholtzDecompositionDecodeFields (ef : EventFlow) : HelmholtzDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  HelmholtzDecompositionUp.mk
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 0 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 1 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 2 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 3 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 4 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 5 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 6 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 7 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 8 ef))
    (helmholtzDecompositionDecodeBHist
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_eventAt 9 ef))

def helmholtzDecompositionFromEventFlow
    (ef : EventFlow) : Option HelmholtzDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (helmholtzDecompositionDecodeFields ef)

private theorem HelmholtzDecompositionTasteGate_single_carrier_alignment_round_trip
    (x : HelmholtzDecompositionUp) :
    helmholtzDecompositionFromEventFlow (helmholtzDecompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H V G D O B T C P N =>
      change
        some
          (HelmholtzDecompositionUp.mk
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist H))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist V))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist G))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist D))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist O))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist B))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist T))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist C))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist P))
            (helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist N))) =
          some (HelmholtzDecompositionUp.mk H V G D O B T C P N)
      rw [HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode H,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode V,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode G,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode D,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode O,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode B,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode T,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode C,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode P,
        HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode N]

private theorem HelmholtzDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HelmholtzDecompositionUp} :
    helmholtzDecompositionToEventFlow x = helmholtzDecompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      helmholtzDecompositionFromEventFlow (helmholtzDecompositionToEventFlow x) =
        helmholtzDecompositionFromEventFlow (helmholtzDecompositionToEventFlow y) :=
    congrArg helmholtzDecompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HelmholtzDecompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HelmholtzDecompositionTasteGate_single_carrier_alignment_round_trip y)))

instance helmholtzDecompositionBHistCarrier : BHistCarrier HelmholtzDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := helmholtzDecompositionToEventFlow
  fromEventFlow := helmholtzDecompositionFromEventFlow

instance helmholtzDecompositionChapterTasteGate :
    ChapterTasteGate HelmholtzDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change helmholtzDecompositionFromEventFlow (helmholtzDecompositionToEventFlow x) = some x
    exact HelmholtzDecompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HelmholtzDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HelmholtzDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  helmholtzDecompositionChapterTasteGate

theorem HelmholtzDecompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      helmholtzDecompositionDecodeBHist (helmholtzDecompositionEncodeBHist h) = h) ∧
      (∀ x : HelmholtzDecompositionUp,
        helmholtzDecompositionFromEventFlow (helmholtzDecompositionToEventFlow x) = some x) ∧
      (∀ x y : HelmholtzDecompositionUp,
        helmholtzDecompositionToEventFlow x = helmholtzDecompositionToEventFlow y → x = y) ∧
      helmholtzDecompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HelmholtzDecompositionTasteGate_single_carrier_alignment_decode_encode,
      ⟨HelmholtzDecompositionTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
          HelmholtzDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.HelmholtzDecompositionUp
