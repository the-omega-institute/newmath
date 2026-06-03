import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceCompletionUp : Type where
  | mk (X S R M L E H C P N : BHist) : CauchySequenceCompletionUp
  deriving DecidableEq

def cauchySequenceCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceCompletionEncodeBHist h

def cauchySequenceCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceCompletionDecodeBHist tail)

private theorem CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchySequenceCompletionDecodeBHist
      (cauchySequenceCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySequenceCompletionFields : CauchySequenceCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceCompletionUp.mk X S R M L E H C P N => [X, S, R, M, L, E, H, C, P, N]

def cauchySequenceCompletionToEventFlow : CauchySequenceCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySequenceCompletionFields x).map cauchySequenceCompletionEncodeBHist

private def cauchySequenceCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceCompletionEventAt index rest

def cauchySequenceCompletionFromEventFlow : EventFlow → Option CauchySequenceCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchySequenceCompletionUp.mk
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 0 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 1 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 2 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 3 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 4 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 5 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 6 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 7 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 8 ef))
          (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEventAt 9 ef)))

private theorem CauchySequenceCompletionTasteGate_single_carrier_alignment_round_trip
    (x : CauchySequenceCompletionUp) :
    cauchySequenceCompletionFromEventFlow
      (cauchySequenceCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X S R M L E H C P N =>
      change
        some
            (CauchySequenceCompletionUp.mk
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist X))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist S))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist R))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist M))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist L))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist E))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist H))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist C))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist P))
              (cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist N))) =
          some (CauchySequenceCompletionUp.mk X S R M L E H C P N)
      rw [CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode X,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode S,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode R,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode M,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode L,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode E,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode H,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode C,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode P,
        CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchySequenceCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySequenceCompletionUp} :
    cauchySequenceCompletionToEventFlow x = cauchySequenceCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceCompletionFromEventFlow (cauchySequenceCompletionToEventFlow x) =
        cauchySequenceCompletionFromEventFlow (cauchySequenceCompletionToEventFlow y) :=
    congrArg cauchySequenceCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchySequenceCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySequenceCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySequenceCompletionBHistCarrier :
    BHistCarrier CauchySequenceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceCompletionToEventFlow
  fromEventFlow := cauchySequenceCompletionFromEventFlow

instance cauchySequenceCompletionChapterTasteGate :
    ChapterTasteGate CauchySequenceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequenceCompletionFromEventFlow
        (cauchySequenceCompletionToEventFlow x) = some x
    exact CauchySequenceCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchySequenceCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchySequenceCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchySequenceCompletionDecodeBHist (cauchySequenceCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchySequenceCompletionUp) ∧
        Nonempty (ChapterTasteGate CauchySequenceCompletionUp) ∧
          cauchySequenceCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchySequenceCompletionTasteGate_single_carrier_alignment_decode_encode,
      ⟨cauchySequenceCompletionBHistCarrier⟩,
      ⟨cauchySequenceCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchySequenceCompletionUp
