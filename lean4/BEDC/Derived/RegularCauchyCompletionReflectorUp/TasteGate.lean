import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionReflectorUp : Type where
  | mk (S Q E U I P H C N : BHist) : RegularCauchyCompletionReflectorUp
  deriving DecidableEq

def regularCauchyCompletionReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionReflectorEncodeBHist h

def regularCauchyCompletionReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionReflectorDecodeBHist tail)

private theorem RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionReflectorFields :
    RegularCauchyCompletionReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionReflectorUp.mk S Q E U I P H C N =>
      [S, Q, E, U, I, P, H, C, N]

def regularCauchyCompletionReflectorToEventFlow :
    RegularCauchyCompletionReflectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyCompletionReflectorFields x).map
      regularCauchyCompletionReflectorEncodeBHist

private def regularCauchyCompletionReflectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCompletionReflectorEventAtDefault index rest

def regularCauchyCompletionReflectorFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCompletionReflectorUp.mk
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 0 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 1 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 2 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 3 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 4 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 5 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 6 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 7 ef))
      (regularCauchyCompletionReflectorDecodeBHist
        (regularCauchyCompletionReflectorEventAtDefault 8 ef)))

private theorem regularCauchyCompletionReflector_round_trip :
    ∀ x : RegularCauchyCompletionReflectorUp,
      regularCauchyCompletionReflectorFromEventFlow
        (regularCauchyCompletionReflectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q E U I P H C N =>
      change
        some
            (RegularCauchyCompletionReflectorUp.mk
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist S))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist Q))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist E))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist U))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist I))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist P))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist H))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist C))
              (regularCauchyCompletionReflectorDecodeBHist
                (regularCauchyCompletionReflectorEncodeBHist N))) =
          some (RegularCauchyCompletionReflectorUp.mk S Q E U I P H C N)
      rw [RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode S,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode E,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode U,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode I,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode P,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode H,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode C,
        RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode N]

private theorem regularCauchyCompletionReflectorToEventFlow_injective
    {x y : RegularCauchyCompletionReflectorUp} :
    regularCauchyCompletionReflectorToEventFlow x =
      regularCauchyCompletionReflectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionReflectorFromEventFlow
          (regularCauchyCompletionReflectorToEventFlow x) =
        regularCauchyCompletionReflectorFromEventFlow
          (regularCauchyCompletionReflectorToEventFlow y) :=
    congrArg regularCauchyCompletionReflectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionReflector_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionReflector_round_trip y)))

instance regularCauchyCompletionReflectorBHistCarrier :
    BHistCarrier RegularCauchyCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionReflectorToEventFlow
  fromEventFlow := regularCauchyCompletionReflectorFromEventFlow

instance regularCauchyCompletionReflectorChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyCompletionReflectorFromEventFlow
      (regularCauchyCompletionReflectorToEventFlow x) = some x
    exact regularCauchyCompletionReflector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionReflectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionReflectorChapterTasteGate

theorem RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyCompletionReflectorDecodeBHist
      (regularCauchyCompletionReflectorEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCompletionReflectorUp,
        regularCauchyCompletionReflectorFromEventFlow
          (regularCauchyCompletionReflectorToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyCompletionReflectorUp,
          regularCauchyCompletionReflectorToEventFlow x =
            regularCauchyCompletionReflectorToEventFlow y → x = y) ∧
          regularCauchyCompletionReflectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyCompletionReflectorTasteGate_single_carrier_alignment_decode,
      regularCauchyCompletionReflector_round_trip,
      (fun _ _ heq => regularCauchyCompletionReflectorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionReflectorUp
