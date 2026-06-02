import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyChainCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyChainCriterionUp : Type where
  | mk (S L W R D E H C P N : BHist) : CauchyChainCriterionUp
  deriving DecidableEq

def cauchyChainCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyChainCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyChainCriterionEncodeBHist h

def cauchyChainCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyChainCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyChainCriterionDecodeBHist tail)

private theorem CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyChainCriterionFields : CauchyChainCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyChainCriterionUp.mk S L W R D E H C P N => [S, L, W, R, D, E, H, C, P, N]

def cauchyChainCriterionToEventFlow : CauchyChainCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyChainCriterionFields x).map cauchyChainCriterionEncodeBHist

private def cauchyChainCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyChainCriterionEventAtDefault index rest

def cauchyChainCriterionFromEventFlow
    (ef : EventFlow) : Option CauchyChainCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyChainCriterionUp.mk
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 0 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 1 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 2 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 3 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 4 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 5 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 6 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 7 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 8 ef))
      (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEventAtDefault 9 ef)))

private theorem CauchyChainCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyChainCriterionUp,
      cauchyChainCriterionFromEventFlow (cauchyChainCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L W R D E H C P N =>
      change
        some
            (CauchyChainCriterionUp.mk
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist S))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist L))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist W))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist R))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist D))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist E))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist H))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist C))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist P))
              (cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist N))) =
          some (CauchyChainCriterionUp.mk S L W R D E H C P N)
      rw [CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode L,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode W,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyChainCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyChainCriterionUp} :
    cauchyChainCriterionToEventFlow x = cauchyChainCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyChainCriterionFromEventFlow (cauchyChainCriterionToEventFlow x) =
        cauchyChainCriterionFromEventFlow (cauchyChainCriterionToEventFlow y) :=
    congrArg cauchyChainCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyChainCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyChainCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyChainCriterionBHistCarrier : BHistCarrier CauchyChainCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyChainCriterionToEventFlow
  fromEventFlow := cauchyChainCriterionFromEventFlow

instance cauchyChainCriterionChapterTasteGate :
    ChapterTasteGate CauchyChainCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyChainCriterionFromEventFlow (cauchyChainCriterionToEventFlow x) = some x
    exact CauchyChainCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyChainCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyChainCriterionTasteGate_single_carrier_alignment :
    (∀ S L W R D E H C P N : BHist,
      cauchyChainCriterionFields (CauchyChainCriterionUp.mk S L W R D E H C P N) =
        [S, L, W, R, D, E, H, C, P, N]) ∧
      cauchyChainCriterionEncodeBHist BHist.Empty = ([] : RawEvent) ∧
        (∀ h : BHist,
          cauchyChainCriterionDecodeBHist (cauchyChainCriterionEncodeBHist h) = h) ∧
          Nonempty (BHistCarrier CauchyChainCriterionUp) ∧
            Nonempty (ChapterTasteGate CauchyChainCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨by intro S L W R D E H C P N; rfl, rfl,
      CauchyChainCriterionTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro cauchyChainCriterionBHistCarrier,
      Nonempty.intro cauchyChainCriterionChapterTasteGate⟩

end BEDC.Derived.CauchyChainCriterionUp
