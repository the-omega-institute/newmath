import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionUnitIsometryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionUnitIsometryUp : Type where
  | mk (S R D U E H C P N : BHist) : CauchyCompletionUnitIsometryUp
  deriving DecidableEq

def cauchyCompletionUnitIsometryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionUnitIsometryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionUnitIsometryEncodeBHist h

def cauchyCompletionUnitIsometryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionUnitIsometryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionUnitIsometryDecodeBHist tail)

private theorem CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionUnitIsometryDecodeBHist
          (cauchyCompletionUnitIsometryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionUnitIsometryFields : CauchyCompletionUnitIsometryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionUnitIsometryUp.mk S R D U E H C P N => [S, R, D, U, E, H, C, P, N]

def cauchyCompletionUnitIsometryToEventFlow :
    CauchyCompletionUnitIsometryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionUnitIsometryFields x).map cauchyCompletionUnitIsometryEncodeBHist

private def cauchyCompletionUnitIsometryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionUnitIsometryEventAtDefault index rest

def cauchyCompletionUnitIsometryFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionUnitIsometryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionUnitIsometryUp.mk
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 0 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 1 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 2 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 3 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 4 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 5 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 6 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 7 ef))
      (cauchyCompletionUnitIsometryDecodeBHist (cauchyCompletionUnitIsometryEventAtDefault 8 ef)))

private theorem CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionUnitIsometryUp,
      cauchyCompletionUnitIsometryFromEventFlow
          (cauchyCompletionUnitIsometryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D U E H C P N =>
      change
        some
          (CauchyCompletionUnitIsometryUp.mk
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist S))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist R))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist D))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist U))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist E))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist H))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist C))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist P))
            (cauchyCompletionUnitIsometryDecodeBHist
              (cauchyCompletionUnitIsometryEncodeBHist N))) =
          some (CauchyCompletionUnitIsometryUp.mk S R D U E H C P N)
      rw [CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode R,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode U,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode N]

private theorem cauchyCompletionUnitIsometryToEventFlow_injective
    {x y : CauchyCompletionUnitIsometryUp} :
    cauchyCompletionUnitIsometryToEventFlow x =
        cauchyCompletionUnitIsometryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionUnitIsometryFromEventFlow
          (cauchyCompletionUnitIsometryToEventFlow x) =
        cauchyCompletionUnitIsometryFromEventFlow
          (cauchyCompletionUnitIsometryToEventFlow y) :=
    congrArg cauchyCompletionUnitIsometryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionUnitIsometryBHistCarrier :
    BHistCarrier CauchyCompletionUnitIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionUnitIsometryToEventFlow
  fromEventFlow := cauchyCompletionUnitIsometryFromEventFlow

instance cauchyCompletionUnitIsometryChapterTasteGate :
    ChapterTasteGate CauchyCompletionUnitIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionUnitIsometryFromEventFlow
          (cauchyCompletionUnitIsometryToEventFlow x) =
        some x
    exact CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionUnitIsometryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionUnitIsometryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionUnitIsometryChapterTasteGate

theorem CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionUnitIsometryDecodeBHist
          (cauchyCompletionUnitIsometryEncodeBHist h) =
        h) ∧
      (∀ x : CauchyCompletionUnitIsometryUp,
        cauchyCompletionUnitIsometryFromEventFlow
            (cauchyCompletionUnitIsometryToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCompletionUnitIsometryUp,
        cauchyCompletionUnitIsometryToEventFlow x =
            cauchyCompletionUnitIsometryToEventFlow y →
          x = y) ∧
      cauchyCompletionUnitIsometryFields (CauchyCompletionUnitIsometryUp.mk S R D U E H C P N) =
        [S, R, D, U, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_decode,
      CauchyCompletionUnitIsometryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => cauchyCompletionUnitIsometryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionUnitIsometryUp
