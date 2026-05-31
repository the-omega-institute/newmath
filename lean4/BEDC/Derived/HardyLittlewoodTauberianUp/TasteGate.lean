import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HardyLittlewoodTauberianUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HardyLittlewoodTauberianUp : Type where
  | mk (S P A L U M R E H C Q N : BHist) : HardyLittlewoodTauberianUp
  deriving DecidableEq

def hardyLittlewoodTauberianEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hardyLittlewoodTauberianEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hardyLittlewoodTauberianEncodeBHist h

def hardyLittlewoodTauberianDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hardyLittlewoodTauberianDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hardyLittlewoodTauberianDecodeBHist tail)

private theorem HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hardyLittlewoodTauberianToEventFlow : HardyLittlewoodTauberianUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HardyLittlewoodTauberianUp.mk S P A L U M R E H C Q N =>
      [[BMark.b0],
        hardyLittlewoodTauberianEncodeBHist S,
        [BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hardyLittlewoodTauberianEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyLittlewoodTauberianEncodeBHist N]

private def HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault index rest

def hardyLittlewoodTauberianFromEventFlow
    (ef : EventFlow) : Option HardyLittlewoodTauberianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HardyLittlewoodTauberianUp.mk
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 17 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 19 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 21 ef))
      (hardyLittlewoodTauberianDecodeBHist
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_eventAtDefault 23 ef)))

private theorem HardyLittlewoodTauberianTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HardyLittlewoodTauberianUp,
      hardyLittlewoodTauberianFromEventFlow
        (hardyLittlewoodTauberianToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S P A L U M R E H C Q N =>
      change
        some
          (HardyLittlewoodTauberianUp.mk
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist S))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist P))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist A))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist L))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist U))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist M))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist R))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist E))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist H))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist C))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist Q))
            (hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist N))) =
          some (HardyLittlewoodTauberianUp.mk S P A L U M R E H C Q N)
      rw [HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode S,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode P,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode A,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode L,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode U,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode M,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode R,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode E,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode H,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode C,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode Q,
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode N]

private theorem HardyLittlewoodTauberianTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HardyLittlewoodTauberianUp} :
    hardyLittlewoodTauberianToEventFlow x =
      hardyLittlewoodTauberianToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hardyLittlewoodTauberianFromEventFlow (hardyLittlewoodTauberianToEventFlow x) =
        hardyLittlewoodTauberianFromEventFlow (hardyLittlewoodTauberianToEventFlow y) :=
    congrArg hardyLittlewoodTauberianFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_round_trip y)))

instance hardyLittlewoodTauberianBHistCarrier :
    BHistCarrier HardyLittlewoodTauberianUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hardyLittlewoodTauberianToEventFlow
  fromEventFlow := hardyLittlewoodTauberianFromEventFlow

instance hardyLittlewoodTauberianChapterTasteGate :
    ChapterTasteGate HardyLittlewoodTauberianUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hardyLittlewoodTauberianFromEventFlow (hardyLittlewoodTauberianToEventFlow x) =
        some x
    exact HardyLittlewoodTauberianTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HardyLittlewoodTauberianTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HardyLittlewoodTauberianTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hardyLittlewoodTauberianDecodeBHist (hardyLittlewoodTauberianEncodeBHist h) = h) ∧
      (∀ x : HardyLittlewoodTauberianUp,
        hardyLittlewoodTauberianFromEventFlow (hardyLittlewoodTauberianToEventFlow x) =
          some x) ∧
      (∀ x y : HardyLittlewoodTauberianUp,
        hardyLittlewoodTauberianToEventFlow x = hardyLittlewoodTauberianToEventFlow y →
          x = y) ∧
      hardyLittlewoodTauberianEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate RawEvent
  exact
    ⟨HardyLittlewoodTauberianTasteGate_single_carrier_alignment_decode,
      HardyLittlewoodTauberianTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HardyLittlewoodTauberianTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HardyLittlewoodTauberianUp
