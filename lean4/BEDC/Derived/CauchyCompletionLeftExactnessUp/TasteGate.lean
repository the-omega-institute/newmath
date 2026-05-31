import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionLeftExactnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionLeftExactnessUp : Type where
  | mk (S U D K E H C P N : BHist) : CauchyCompletionLeftExactnessUp
  deriving DecidableEq

def cauchyCompletionLeftExactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionLeftExactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionLeftExactnessEncodeBHist h

def cauchyCompletionLeftExactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionLeftExactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionLeftExactnessDecodeBHist tail)

private theorem CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionLeftExactnessDecodeBHist
        (cauchyCompletionLeftExactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionLeftExactnessFields :
    CauchyCompletionLeftExactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionLeftExactnessUp.mk S U D K E H C P N => [S, U, D, K, E, H, C, P, N]

def cauchyCompletionLeftExactnessToEventFlow :
    CauchyCompletionLeftExactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionLeftExactnessFields x).map
      cauchyCompletionLeftExactnessEncodeBHist

private def cauchyCompletionLeftExactnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionLeftExactnessEventAt index rest

def cauchyCompletionLeftExactnessFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionLeftExactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionLeftExactnessUp.mk
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 0 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 1 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 2 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 3 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 4 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 5 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 6 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 7 ef))
      (cauchyCompletionLeftExactnessDecodeBHist (cauchyCompletionLeftExactnessEventAt 8 ef)))

private theorem CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletionLeftExactnessUp) :
    cauchyCompletionLeftExactnessFromEventFlow
      (cauchyCompletionLeftExactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S U D K E H C P N =>
      change
        some
          (CauchyCompletionLeftExactnessUp.mk
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist S))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist U))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist D))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist K))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist E))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist H))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist C))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist P))
            (cauchyCompletionLeftExactnessDecodeBHist
              (cauchyCompletionLeftExactnessEncodeBHist N))) =
          some (CauchyCompletionLeftExactnessUp.mk S U D K E H C P N)
      rw [CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode K,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionLeftExactnessUp} :
    cauchyCompletionLeftExactnessToEventFlow x =
      cauchyCompletionLeftExactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionLeftExactnessFromEventFlow
          (cauchyCompletionLeftExactnessToEventFlow x) =
        cauchyCompletionLeftExactnessFromEventFlow
          (cauchyCompletionLeftExactnessToEventFlow y) :=
    congrArg cauchyCompletionLeftExactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionLeftExactnessBHistCarrier :
    BHistCarrier CauchyCompletionLeftExactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionLeftExactnessToEventFlow
  fromEventFlow := cauchyCompletionLeftExactnessFromEventFlow

instance cauchyCompletionLeftExactnessChapterTasteGate :
    ChapterTasteGate CauchyCompletionLeftExactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionLeftExactnessFromEventFlow
        (cauchyCompletionLeftExactnessToEventFlow x) = some x
    exact CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyCompletionLeftExactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionLeftExactnessChapterTasteGate

theorem CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionLeftExactnessDecodeBHist
        (cauchyCompletionLeftExactnessEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionLeftExactnessUp,
        cauchyCompletionLeftExactnessFromEventFlow
          (cauchyCompletionLeftExactnessToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionLeftExactnessUp,
          cauchyCompletionLeftExactnessToEventFlow x =
            cauchyCompletionLeftExactnessToEventFlow y → x = y) ∧
          cauchyCompletionLeftExactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionLeftExactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionLeftExactnessUp.TasteGate
