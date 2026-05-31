import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyCompletenessUp : Type where
  | mk (S M D R L E H C P N : BHist) : RealCauchyCompletenessUp
  deriving DecidableEq

def realCauchyCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyCompletenessEncodeBHist h

def realCauchyCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyCompletenessDecodeBHist tail)

private theorem RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realCauchyCompletenessDecodeBHist
        (realCauchyCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyCompletenessFields : RealCauchyCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyCompletenessUp.mk S M D R L E H C P N =>
      [S, M, D, R, L, E, H, C, P, N]

def realCauchyCompletenessToEventFlow :
    RealCauchyCompletenessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realCauchyCompletenessFields x).map realCauchyCompletenessEncodeBHist

private def realCauchyCompletenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyCompletenessEventAtDefault index rest

def realCauchyCompletenessFromEventFlow
    (ef : EventFlow) : Option RealCauchyCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCauchyCompletenessUp.mk
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 0 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 1 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 2 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 3 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 4 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 5 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 6 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 7 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 8 ef))
      (realCauchyCompletenessDecodeBHist (realCauchyCompletenessEventAtDefault 9 ef)))

private theorem RealCauchyCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealCauchyCompletenessUp,
      realCauchyCompletenessFromEventFlow
        (realCauchyCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D R L E H C P N =>
      change
        some
            (RealCauchyCompletenessUp.mk
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist S))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist M))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist D))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist R))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist L))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist E))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist H))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist C))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist P))
              (realCauchyCompletenessDecodeBHist
                (realCauchyCompletenessEncodeBHist N))) =
          some (RealCauchyCompletenessUp.mk S M D R L E H C P N)
      rw [RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode S,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode M,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode D,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode R,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode L,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode E,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode H,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode C,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode P,
        RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealCauchyCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealCauchyCompletenessUp} :
    realCauchyCompletenessToEventFlow x = realCauchyCompletenessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyCompletenessFromEventFlow (realCauchyCompletenessToEventFlow x) =
        realCauchyCompletenessFromEventFlow (realCauchyCompletenessToEventFlow y) :=
    congrArg realCauchyCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealCauchyCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealCauchyCompletenessTasteGate_single_carrier_alignment_round_trip y)))

instance realCauchyCompletenessBHistCarrier :
    BHistCarrier RealCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyCompletenessToEventFlow
  fromEventFlow := realCauchyCompletenessFromEventFlow

instance realCauchyCompletenessChapterTasteGate :
    ChapterTasteGate RealCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCauchyCompletenessFromEventFlow
        (realCauchyCompletenessToEventFlow x) = some x
    exact RealCauchyCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealCauchyCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealCauchyCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realCauchyCompletenessDecodeBHist
          (realCauchyCompletenessEncodeBHist h) = h) ∧
      (∀ x : RealCauchyCompletenessUp,
        realCauchyCompletenessFromEventFlow
          (realCauchyCompletenessToEventFlow x) = some x) ∧
        (∀ x y : RealCauchyCompletenessUp,
          realCauchyCompletenessToEventFlow x =
              realCauchyCompletenessToEventFlow y →
            x = y) ∧
          realCauchyCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealCauchyCompletenessTasteGate_single_carrier_alignment_decode_encode,
      RealCauchyCompletenessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealCauchyCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealCauchyCompletenessUp
