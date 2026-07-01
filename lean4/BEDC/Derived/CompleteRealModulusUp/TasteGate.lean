import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteRealModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteRealModulusUp : Type where
  | mk : (F S D R Q E H C P N : BHist) → CompleteRealModulusUp
  deriving DecidableEq

def completeRealModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeRealModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeRealModulusEncodeBHist h

def completeRealModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeRealModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeRealModulusDecodeBHist tail)

private theorem CompleteRealModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, completeRealModulusDecodeBHist (completeRealModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeRealModulusFields : CompleteRealModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteRealModulusUp.mk F S D R Q E H C P N => [F, S, D, R, Q, E, H, C, P, N]

def completeRealModulusToEventFlow : CompleteRealModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completeRealModulusFields x).map completeRealModulusEncodeBHist

private def completeRealModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completeRealModulusEventAt index rest

def completeRealModulusFromEventFlow : EventFlow → Option CompleteRealModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompleteRealModulusUp.mk
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 0 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 1 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 2 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 3 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 4 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 5 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 6 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 7 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 8 ef))
        (completeRealModulusDecodeBHist (completeRealModulusEventAt 9 ef)))

private theorem CompleteRealModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompleteRealModulusUp,
      completeRealModulusFromEventFlow (completeRealModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S D R Q E H C P N =>
      change
        some
          (CompleteRealModulusUp.mk
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist F))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist S))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist D))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist R))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist Q))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist E))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist H))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist C))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist P))
            (completeRealModulusDecodeBHist (completeRealModulusEncodeBHist N))) =
          some (CompleteRealModulusUp.mk F S D R Q E H C P N)
      rw [CompleteRealModulusTasteGate_single_carrier_alignment_decode F,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode S,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode D,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode R,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode Q,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode E,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode H,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode C,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode P,
        CompleteRealModulusTasteGate_single_carrier_alignment_decode N]

private theorem CompleteRealModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompleteRealModulusUp} :
    completeRealModulusToEventFlow x = completeRealModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeRealModulusFromEventFlow (completeRealModulusToEventFlow x) =
        completeRealModulusFromEventFlow (completeRealModulusToEventFlow y) :=
    congrArg completeRealModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompleteRealModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompleteRealModulusTasteGate_single_carrier_alignment_round_trip y)))

instance completeRealModulusBHistCarrier : BHistCarrier CompleteRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeRealModulusToEventFlow
  fromEventFlow := completeRealModulusFromEventFlow

instance completeRealModulusChapterTasteGate : ChapterTasteGate CompleteRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeRealModulusFromEventFlow (completeRealModulusToEventFlow x) = some x
    exact CompleteRealModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompleteRealModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompleteRealModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, completeRealModulusDecodeBHist (completeRealModulusEncodeBHist h) = h) ∧
      (∀ x : CompleteRealModulusUp,
        completeRealModulusFromEventFlow (completeRealModulusToEventFlow x) = some x) ∧
        (∀ x y : CompleteRealModulusUp,
          completeRealModulusToEventFlow x = completeRealModulusToEventFlow y → x = y) ∧
          completeRealModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompleteRealModulusTasteGate_single_carrier_alignment_decode,
      CompleteRealModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompleteRealModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompleteRealModulusUp
