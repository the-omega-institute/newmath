import BEDC.Derived.JordanDecompositionBoundedVariationUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.JordanDecompositionBoundedVariationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def jordanDecompositionBoundedVariationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: jordanDecompositionBoundedVariationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: jordanDecompositionBoundedVariationEncodeBHist h

def jordanDecompositionBoundedVariationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (jordanDecompositionBoundedVariationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (jordanDecompositionBoundedVariationDecodeBHist tail)

private theorem JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      jordanDecompositionBoundedVariationDecodeBHist
          (jordanDecompositionBoundedVariationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_fields :
    JordanDecompositionBoundedVariationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | JordanDecompositionBoundedVariationUp.mk B L Ppos Pneg M R D E H C Q N =>
      [B, L, Ppos, Pneg, M, R, D, E, H, C, Q, N]

def jordanDecompositionBoundedVariationToEventFlow :
    JordanDecompositionBoundedVariationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_fields x).map
        jordanDecompositionBoundedVariationEncodeBHist

private def jordanDecompositionBoundedVariationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      jordanDecompositionBoundedVariationEventAtDefault index rest

def jordanDecompositionBoundedVariationFromEventFlow
    (ef : EventFlow) : Option JordanDecompositionBoundedVariationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (JordanDecompositionBoundedVariationUp.mk
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 0 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 1 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 2 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 3 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 4 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 5 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 6 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 7 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 8 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 9 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 10 ef))
      (jordanDecompositionBoundedVariationDecodeBHist
        (jordanDecompositionBoundedVariationEventAtDefault 11 ef)))

private theorem JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : JordanDecompositionBoundedVariationUp,
      jordanDecompositionBoundedVariationFromEventFlow
          (jordanDecompositionBoundedVariationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L Ppos Pneg M R D E H C Q N =>
      change
        some
          (JordanDecompositionBoundedVariationUp.mk
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist B))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist L))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist Ppos))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist Pneg))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist M))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist R))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist D))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist E))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist H))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist C))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist Q))
            (jordanDecompositionBoundedVariationDecodeBHist
              (jordanDecompositionBoundedVariationEncodeBHist N))) =
          some
            (JordanDecompositionBoundedVariationUp.mk B L Ppos Pneg M R D E H C Q N)
      rw [
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode B,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode L,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode Ppos,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode Pneg,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode M,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode R,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode D,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode E,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode H,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode C,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode Q,
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode N]

private theorem JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : JordanDecompositionBoundedVariationUp} :
    jordanDecompositionBoundedVariationToEventFlow x =
        jordanDecompositionBoundedVariationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      jordanDecompositionBoundedVariationFromEventFlow
          (jordanDecompositionBoundedVariationToEventFlow x) =
        jordanDecompositionBoundedVariationFromEventFlow
          (jordanDecompositionBoundedVariationToEventFlow y) :=
    congrArg jordanDecompositionBoundedVariationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_round_trip y)))

instance jordanDecompositionBoundedVariationBHistCarrier :
    BHistCarrier JordanDecompositionBoundedVariationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := jordanDecompositionBoundedVariationToEventFlow
  fromEventFlow := jordanDecompositionBoundedVariationFromEventFlow

instance jordanDecompositionBoundedVariationChapterTasteGate :
    ChapterTasteGate JordanDecompositionBoundedVariationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change jordanDecompositionBoundedVariationFromEventFlow
      (jordanDecompositionBoundedVariationToEventFlow x) = some x
    exact JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate JordanDecompositionBoundedVariationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  jordanDecompositionBoundedVariationChapterTasteGate

theorem JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      jordanDecompositionBoundedVariationDecodeBHist
          (jordanDecompositionBoundedVariationEncodeBHist h) = h) ∧
      (∀ x : JordanDecompositionBoundedVariationUp,
        jordanDecompositionBoundedVariationFromEventFlow
          (jordanDecompositionBoundedVariationToEventFlow x) = some x) ∧
      (∀ x y : JordanDecompositionBoundedVariationUp,
        jordanDecompositionBoundedVariationToEventFlow x =
            jordanDecompositionBoundedVariationToEventFlow y →
          x = y) ∧
      jordanDecompositionBoundedVariationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_decode,
      JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        JordanDecompositionBoundedVariationTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.JordanDecompositionBoundedVariationUp
