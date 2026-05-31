import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RaikovCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RaikovCompletionUp : Type where
  | mk (G U S L R F C H P N : BHist) : RaikovCompletionUp
  deriving DecidableEq

def raikovCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: raikovCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: raikovCompletionEncodeBHist h

def raikovCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (raikovCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (raikovCompletionDecodeBHist tail)

private theorem RaikovCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, raikovCompletionDecodeBHist (raikovCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def raikovCompletionFields : RaikovCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RaikovCompletionUp.mk G U S L R F C H P N => [G, U, S, L, R, F, C, H, P, N]

def raikovCompletionToEventFlow : RaikovCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (raikovCompletionFields token).map raikovCompletionEncodeBHist

private def raikovCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => raikovCompletionEventAtDefault index rest

def raikovCompletionFromEventFlow (ef : EventFlow) : Option RaikovCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RaikovCompletionUp.mk
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 0 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 1 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 2 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 3 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 4 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 5 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 6 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 7 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 8 ef))
      (raikovCompletionDecodeBHist (raikovCompletionEventAtDefault 9 ef)))

private theorem RaikovCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RaikovCompletionUp,
      raikovCompletionFromEventFlow (raikovCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk G U S L R F C H P N =>
      change
        some
          (RaikovCompletionUp.mk
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist G))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist U))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist S))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist L))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist R))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist F))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist C))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist H))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist P))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist N))) =
          some (RaikovCompletionUp.mk G U S L R F C H P N)
      rw [RaikovCompletionTasteGate_single_carrier_alignment_decode G,
        RaikovCompletionTasteGate_single_carrier_alignment_decode U,
        RaikovCompletionTasteGate_single_carrier_alignment_decode S,
        RaikovCompletionTasteGate_single_carrier_alignment_decode L,
        RaikovCompletionTasteGate_single_carrier_alignment_decode R,
        RaikovCompletionTasteGate_single_carrier_alignment_decode F,
        RaikovCompletionTasteGate_single_carrier_alignment_decode C,
        RaikovCompletionTasteGate_single_carrier_alignment_decode H,
        RaikovCompletionTasteGate_single_carrier_alignment_decode P,
        RaikovCompletionTasteGate_single_carrier_alignment_decode N]

private theorem RaikovCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RaikovCompletionUp} :
    raikovCompletionToEventFlow x = raikovCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      raikovCompletionFromEventFlow (raikovCompletionToEventFlow x) =
        raikovCompletionFromEventFlow (raikovCompletionToEventFlow y) :=
    congrArg raikovCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RaikovCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RaikovCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance raikovCompletionBHistCarrier : BHistCarrier RaikovCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := raikovCompletionToEventFlow
  fromEventFlow := raikovCompletionFromEventFlow

instance raikovCompletionChapterTasteGate : ChapterTasteGate RaikovCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change raikovCompletionFromEventFlow (raikovCompletionToEventFlow x) = some x
    exact RaikovCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RaikovCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RaikovCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, raikovCompletionDecodeBHist (raikovCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RaikovCompletionUp) ∧
        Nonempty (ChapterTasteGate RaikovCompletionUp) ∧
          raikovCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RaikovCompletionTasteGate_single_carrier_alignment_decode,
      ⟨raikovCompletionBHistCarrier⟩,
      ⟨raikovCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RaikovCompletionUp
