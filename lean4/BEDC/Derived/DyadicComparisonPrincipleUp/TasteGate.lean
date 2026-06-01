import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicComparisonPrincipleUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicComparisonPrincipleUp : Type where
  | mk (D0 D1 W R O H C P N : BHist) : DyadicComparisonPrincipleUp
  deriving DecidableEq

def dyadicComparisonPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicComparisonPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicComparisonPrincipleEncodeBHist h

def dyadicComparisonPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicComparisonPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicComparisonPrincipleDecodeBHist tail)

private theorem DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicComparisonPrincipleFields : DyadicComparisonPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicComparisonPrincipleUp.mk D0 D1 W R O H C P N => [D0, D1, W, R, O, H, C, P, N]

def dyadicComparisonPrincipleToEventFlow : DyadicComparisonPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicComparisonPrincipleFields x).map dyadicComparisonPrincipleEncodeBHist

private def dyadicComparisonPrincipleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicComparisonPrincipleEventAt index rest

def dyadicComparisonPrincipleFromEventFlow
    (ef : EventFlow) : Option DyadicComparisonPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicComparisonPrincipleUp.mk
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 0 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 1 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 2 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 3 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 4 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 5 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 6 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 7 ef))
      (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEventAt 8 ef)))

private theorem DyadicComparisonPrincipleTasteGate_single_carrier_alignment_round_trip
    (x : DyadicComparisonPrincipleUp) :
    dyadicComparisonPrincipleFromEventFlow (dyadicComparisonPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D0 D1 W R O H C P N =>
      change
        some
          (DyadicComparisonPrincipleUp.mk
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist D0))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist D1))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist W))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist R))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist O))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist H))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist C))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist P))
            (dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist N))) =
          some (DyadicComparisonPrincipleUp.mk D0 D1 W R O H C P N)
      rw [DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode D0,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode D1,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode W,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode R,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode O,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode H,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode C,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode P,
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicComparisonPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicComparisonPrincipleUp} :
    dyadicComparisonPrincipleToEventFlow x = dyadicComparisonPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicComparisonPrincipleFromEventFlow (dyadicComparisonPrincipleToEventFlow x) =
        dyadicComparisonPrincipleFromEventFlow (dyadicComparisonPrincipleToEventFlow y) :=
    congrArg dyadicComparisonPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicComparisonPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicComparisonPrincipleBHistCarrier : BHistCarrier DyadicComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicComparisonPrincipleToEventFlow
  fromEventFlow := dyadicComparisonPrincipleFromEventFlow

instance dyadicComparisonPrincipleChapterTasteGate :
    ChapterTasteGate DyadicComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicComparisonPrincipleFromEventFlow
      (dyadicComparisonPrincipleToEventFlow x) = some x
    exact DyadicComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicComparisonPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def DyadicComparisonPrincipleTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DyadicComparisonPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicComparisonPrincipleChapterTasteGate

theorem DyadicComparisonPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicComparisonPrincipleDecodeBHist (dyadicComparisonPrincipleEncodeBHist h) = h) ∧
      (∀ x : DyadicComparisonPrincipleUp,
        dyadicComparisonPrincipleFromEventFlow
          (dyadicComparisonPrincipleToEventFlow x) = some x) ∧
        (∀ x y : DyadicComparisonPrincipleUp,
          dyadicComparisonPrincipleToEventFlow x =
            dyadicComparisonPrincipleToEventFlow y → x = y) ∧
          dyadicComparisonPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode,
      DyadicComparisonPrincipleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicComparisonPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicComparisonPrincipleUp.TasteGate
