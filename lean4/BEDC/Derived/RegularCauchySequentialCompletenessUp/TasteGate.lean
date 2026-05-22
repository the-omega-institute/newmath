import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySequentialCompletenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySequentialCompletenessUp : Type where
  | mk (D S R M L U H C P N : BHist) : RegularCauchySequentialCompletenessUp
  deriving DecidableEq

def regularCauchySequentialCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySequentialCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySequentialCompletenessEncodeBHist h

def regularCauchySequentialCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySequentialCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySequentialCompletenessDecodeBHist tail)

private theorem RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySequentialCompletenessFields :
    RegularCauchySequentialCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySequentialCompletenessUp.mk D S R M L U H C P N =>
      [D, S, R, M, L, U, H, C, P, N]

def regularCauchySequentialCompletenessToEventFlow :
    RegularCauchySequentialCompletenessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchySequentialCompletenessFields x).map
      regularCauchySequentialCompletenessEncodeBHist

private def regularCauchySequentialCompletenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchySequentialCompletenessEventAtDefault index rest

def regularCauchySequentialCompletenessFromEventFlow
    (ef : EventFlow) : Option RegularCauchySequentialCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySequentialCompletenessUp.mk
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 0 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 1 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 2 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 3 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 4 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 5 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 6 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 7 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 8 ef))
      (regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEventAtDefault 9 ef)))

private theorem RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySequentialCompletenessUp,
      regularCauchySequentialCompletenessFromEventFlow
          (regularCauchySequentialCompletenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk D S R M L U H C P N =>
      change
        some
          (RegularCauchySequentialCompletenessUp.mk
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist D))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist S))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist R))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist M))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist L))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist U))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist H))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist C))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist P))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist N))) =
          some (RegularCauchySequentialCompletenessUp.mk D S R M L U H C P N)
      rw [RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode D,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode S,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode R,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode M,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode L,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode U,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode H,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode C,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode P,
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode N]

private theorem
    RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySequentialCompletenessUp} :
    regularCauchySequentialCompletenessToEventFlow x =
      regularCauchySequentialCompletenessToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      regularCauchySequentialCompletenessFromEventFlow
          (regularCauchySequentialCompletenessToEventFlow x) =
        regularCauchySequentialCompletenessFromEventFlow
          (regularCauchySequentialCompletenessToEventFlow y) :=
    congrArg regularCauchySequentialCompletenessFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans
      (RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySequentialCompletenessBHistCarrier :
    BHistCarrier RegularCauchySequentialCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySequentialCompletenessToEventFlow
  fromEventFlow := regularCauchySequentialCompletenessFromEventFlow

instance regularCauchySequentialCompletenessChapterTasteGate :
    ChapterTasteGate RegularCauchySequentialCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySequentialCompletenessFromEventFlow
          (regularCauchySequentialCompletenessToEventFlow x) =
        some x
    exact RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySequentialCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySequentialCompletenessChapterTasteGate

theorem RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySequentialCompletenessUp,
        regularCauchySequentialCompletenessFromEventFlow
            (regularCauchySequentialCompletenessToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchySequentialCompletenessUp,
          regularCauchySequentialCompletenessToEventFlow x =
              regularCauchySequentialCompletenessToEventFlow y →
            x = y) ∧
          regularCauchySequentialCompletenessEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_decode,
      RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchySequentialCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchySequentialCompletenessUp.TasteGate
