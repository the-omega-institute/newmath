import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SummableTailModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SummableTailModulusUp : Type where
  | mk (M D S R B E H C P N : BHist) : SummableTailModulusUp
  deriving DecidableEq

def summableTailModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: summableTailModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: summableTailModulusEncodeBHist h

def summableTailModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (summableTailModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (summableTailModulusDecodeBHist tail)

private theorem SummableTailModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      summableTailModulusDecodeBHist (summableTailModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def summableTailModulusFields : SummableTailModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SummableTailModulusUp.mk M D S R B E H C P N => [M, D, S, R, B, E, H, C, P, N]

def summableTailModulusToEventFlow : SummableTailModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (summableTailModulusFields x).map summableTailModulusEncodeBHist

private def summableTailModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => summableTailModulusEventAt index rest

def summableTailModulusFromEventFlow (ef : EventFlow) : Option SummableTailModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SummableTailModulusUp.mk
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 0 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 1 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 2 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 3 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 4 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 5 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 6 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 7 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 8 ef))
      (summableTailModulusDecodeBHist (summableTailModulusEventAt 9 ef)))

private theorem SummableTailModulusTasteGate_single_carrier_alignment_round_trip
    (x : SummableTailModulusUp) :
    summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M D S R B E H C P N =>
      change
        some
          (SummableTailModulusUp.mk
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist M))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist D))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist S))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist R))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist B))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist E))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist H))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist C))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist P))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist N))) =
          some (SummableTailModulusUp.mk M D S R B E H C P N)
      rw [SummableTailModulusTasteGate_single_carrier_alignment_decode_encode M,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode D,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode S,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode R,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode B,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode E,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode H,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode C,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode P,
        SummableTailModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem SummableTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SummableTailModulusUp} :
    summableTailModulusToEventFlow x = summableTailModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) =
        summableTailModulusFromEventFlow (summableTailModulusToEventFlow y) :=
    congrArg summableTailModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SummableTailModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SummableTailModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem SummableTailModulusTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SummableTailModulusUp,
      summableTailModulusFields x = summableTailModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ D₁ S₁ R₁ B₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ D₂ S₂ R₂ B₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance summableTailModulusBHistCarrier : BHistCarrier SummableTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := summableTailModulusToEventFlow
  fromEventFlow := summableTailModulusFromEventFlow

instance summableTailModulusChapterTasteGate : ChapterTasteGate SummableTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) = some x
    exact SummableTailModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SummableTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance summableTailModulusFieldFaithful : FieldFaithful SummableTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := summableTailModulusFields
  field_faithful := SummableTailModulusTasteGate_single_carrier_alignment_fields_faithful

instance summableTailModulusNontrivial : Nontrivial SummableTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SummableTailModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SummableTailModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def SummableTailModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate SummableTailModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  summableTailModulusChapterTasteGate

theorem SummableTailModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, summableTailModulusDecodeBHist (summableTailModulusEncodeBHist h) = h) ∧
      (∀ x : SummableTailModulusUp,
        summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) = some x) ∧
        (∀ x y : SummableTailModulusUp,
          summableTailModulusToEventFlow x = summableTailModulusToEventFlow y → x = y) ∧
          summableTailModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SummableTailModulusTasteGate_single_carrier_alignment_decode_encode,
      SummableTailModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SummableTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SummableTailModulusUp
