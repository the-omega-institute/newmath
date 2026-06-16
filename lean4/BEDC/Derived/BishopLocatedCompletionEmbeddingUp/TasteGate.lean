import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCompletionEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCompletionEmbeddingUp : Type where
  | mk (M L D E R H C P N : BHist) : BishopLocatedCompletionEmbeddingUp
  deriving DecidableEq

def bishopLocatedCompletionEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCompletionEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCompletionEmbeddingEncodeBHist h

def bishopLocatedCompletionEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCompletionEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCompletionEmbeddingDecodeBHist tail)

private theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCompletionEmbeddingFields :
    BishopLocatedCompletionEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCompletionEmbeddingUp.mk M L D E R H C P N => [M, L, D, E, R, H, C, P, N]

def bishopLocatedCompletionEmbeddingToEventFlow :
    BishopLocatedCompletionEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopLocatedCompletionEmbeddingFields x).map bishopLocatedCompletionEmbeddingEncodeBHist

private def bishopLocatedCompletionEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedCompletionEmbeddingEventAtDefault index rest

def bishopLocatedCompletionEmbeddingFromEventFlow
    (ef : EventFlow) : Option BishopLocatedCompletionEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedCompletionEmbeddingUp.mk
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 0 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 1 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 2 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 3 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 4 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 5 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 6 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 7 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAtDefault 8 ef)))

private theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedCompletionEmbeddingUp,
      bishopLocatedCompletionEmbeddingFromEventFlow
        (bishopLocatedCompletionEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M L D E R H C P N =>
      change
        some
          (BishopLocatedCompletionEmbeddingUp.mk
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist M))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist L))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist D))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist E))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist R))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist H))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist C))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist P))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist N))) =
          some (BishopLocatedCompletionEmbeddingUp.mk M L D E R H C P N)
      rw [BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode M,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode L,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode D,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode E,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode R,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode H,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode C,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode P,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedCompletionEmbeddingUp} :
    bishopLocatedCompletionEmbeddingToEventFlow x =
      bishopLocatedCompletionEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCompletionEmbeddingFromEventFlow
          (bishopLocatedCompletionEmbeddingToEventFlow x) =
        bishopLocatedCompletionEmbeddingFromEventFlow
          (bishopLocatedCompletionEmbeddingToEventFlow y) :=
    congrArg bishopLocatedCompletionEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedCompletionEmbeddingBHistCarrier :
    BHistCarrier BishopLocatedCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCompletionEmbeddingToEventFlow
  fromEventFlow := bishopLocatedCompletionEmbeddingFromEventFlow

instance bishopLocatedCompletionEmbeddingChapterTasteGate :
    ChapterTasteGate BishopLocatedCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedCompletionEmbeddingFromEventFlow
          (bishopLocatedCompletionEmbeddingToEventFlow x) = some x
    exact BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate BishopLocatedCompletionEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCompletionEmbeddingChapterTasteGate

theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedCompletionEmbeddingUp,
        bishopLocatedCompletionEmbeddingFromEventFlow
          (bishopLocatedCompletionEmbeddingToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedCompletionEmbeddingUp,
          bishopLocatedCompletionEmbeddingToEventFlow x =
            bishopLocatedCompletionEmbeddingToEventFlow y → x = y) ∧
          bishopLocatedCompletionEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode,
      BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BishopLocatedCompletionEmbeddingUp
