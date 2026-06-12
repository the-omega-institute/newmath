import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CounterfactualOutcomeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CounterfactualOutcomeUp : Type where
  | mk (U I Yf Ycf M R H D E T P N : BHist) : CounterfactualOutcomeUp
  deriving DecidableEq

def counterfactualOutcomeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: counterfactualOutcomeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: counterfactualOutcomeEncodeBHist h

def counterfactualOutcomeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (counterfactualOutcomeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (counterfactualOutcomeDecodeBHist tail)

private theorem CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def counterfactualOutcomeFields : CounterfactualOutcomeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CounterfactualOutcomeUp.mk U I Yf Ycf M R H D E T P N =>
      [U, I, Yf, Ycf, M, R, H, D, E, T, P, N]

def counterfactualOutcomeToEventFlow : CounterfactualOutcomeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (counterfactualOutcomeFields x).map counterfactualOutcomeEncodeBHist

private def counterfactualOutcomeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => counterfactualOutcomeEventAt index rest

def counterfactualOutcomeFromEventFlow (ef : EventFlow) : Option CounterfactualOutcomeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CounterfactualOutcomeUp.mk
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 0 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 1 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 2 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 3 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 4 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 5 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 6 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 7 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 8 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 9 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 10 ef))
      (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEventAt 11 ef)))

private theorem CounterfactualOutcomeTasteGate_single_carrier_alignment_round_trip
    (x : CounterfactualOutcomeUp) :
    counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U I Yf Ycf M R H D E T P N =>
      change
        some
            (CounterfactualOutcomeUp.mk
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist U))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist I))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist Yf))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist Ycf))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist M))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist R))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist H))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist D))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist E))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist T))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist P))
              (counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist N))) =
          some (CounterfactualOutcomeUp.mk U I Yf Ycf M R H D E T P N)
      rw [CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode U,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode I,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode Yf,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode Ycf,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode M,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode R,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode H,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode D,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode E,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode T,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode P,
        CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode N]

private theorem CounterfactualOutcomeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CounterfactualOutcomeUp} :
    counterfactualOutcomeToEventFlow x = counterfactualOutcomeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) =
        counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow y) :=
    congrArg counterfactualOutcomeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CounterfactualOutcomeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CounterfactualOutcomeTasteGate_single_carrier_alignment_round_trip y)))

instance counterfactualOutcomeBHistCarrier : BHistCarrier CounterfactualOutcomeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := counterfactualOutcomeToEventFlow
  fromEventFlow := counterfactualOutcomeFromEventFlow

instance counterfactualOutcomeChapterTasteGate : ChapterTasteGate CounterfactualOutcomeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change counterfactualOutcomeFromEventFlow (counterfactualOutcomeToEventFlow x) = some x
    exact CounterfactualOutcomeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CounterfactualOutcomeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def counterfactualOutcomeTasteGate : ChapterTasteGate CounterfactualOutcomeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  counterfactualOutcomeChapterTasteGate

theorem CounterfactualOutcomeTasteGate_single_carrier_alignment :
    (∀ h : BHist, counterfactualOutcomeDecodeBHist (counterfactualOutcomeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CounterfactualOutcomeUp) ∧
        Nonempty (ChapterTasteGate CounterfactualOutcomeUp) ∧
          counterfactualOutcomeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CounterfactualOutcomeTasteGate_single_carrier_alignment_decode_encode,
      ⟨counterfactualOutcomeBHistCarrier⟩,
      ⟨counterfactualOutcomeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CounterfactualOutcomeUp
