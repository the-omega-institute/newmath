import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RectifiableCurveUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RectifiableCurveUp : Type where
  | mk (X d gamma I Pi L R H C P N : BHist) : RectifiableCurveUp
  deriving DecidableEq

def rectifiableCurveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rectifiableCurveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rectifiableCurveEncodeBHist h

def rectifiableCurveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rectifiableCurveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rectifiableCurveDecodeBHist tail)

private theorem RectifiableCurveTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rectifiableCurveFields : RectifiableCurveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RectifiableCurveUp.mk X d gamma I Pi L R H C P N => [X, d, gamma, I, Pi, L, R, H, C, P, N]

def rectifiableCurveToEventFlow : RectifiableCurveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rectifiableCurveFields x).map rectifiableCurveEncodeBHist

private def rectifiableCurveEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rectifiableCurveEventAt index rest

def rectifiableCurveFromEventFlow (ef : EventFlow) : Option RectifiableCurveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RectifiableCurveUp.mk
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 0 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 1 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 2 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 3 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 4 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 5 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 6 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 7 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 8 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 9 ef))
      (rectifiableCurveDecodeBHist (rectifiableCurveEventAt 10 ef)))

private theorem RectifiableCurveTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RectifiableCurveUp,
      rectifiableCurveFromEventFlow (rectifiableCurveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d gamma I Pi L R H C P N =>
      change
        some
            (RectifiableCurveUp.mk
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist X))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist d))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist gamma))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist I))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist Pi))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist L))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist R))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist H))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist C))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist P))
              (rectifiableCurveDecodeBHist (rectifiableCurveEncodeBHist N))) =
          some (RectifiableCurveUp.mk X d gamma I Pi L R H C P N)
      rw [RectifiableCurveTasteGate_single_carrier_alignment_decode_encode X,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode d,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode gamma,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode I,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode Pi,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode L,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode R,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode H,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode C,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode P,
        RectifiableCurveTasteGate_single_carrier_alignment_decode_encode N]

private theorem RectifiableCurveToEventFlow_injective {x y : RectifiableCurveUp} :
    rectifiableCurveToEventFlow x = rectifiableCurveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rectifiableCurveFromEventFlow (rectifiableCurveToEventFlow x) =
        rectifiableCurveFromEventFlow (rectifiableCurveToEventFlow y) :=
    congrArg rectifiableCurveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RectifiableCurveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RectifiableCurveTasteGate_single_carrier_alignment_round_trip y)))

instance rectifiableCurveBHistCarrier : BHistCarrier RectifiableCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rectifiableCurveToEventFlow
  fromEventFlow := rectifiableCurveFromEventFlow

instance rectifiableCurveChapterTasteGate : ChapterTasteGate RectifiableCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rectifiableCurveFromEventFlow (rectifiableCurveToEventFlow x) = some x
    exact RectifiableCurveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RectifiableCurveToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RectifiableCurveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rectifiableCurveChapterTasteGate

theorem RectifiableCurveTasteGate_single_carrier_alignment :
    (forall X d gamma I Pi L R H C P N : BHist,
      rectifiableCurveFields (RectifiableCurveUp.mk X d gamma I Pi L R H C P N) =
        [X, d, gamma, I, Pi, L, R, H, C, P, N]) ∧
      rectifiableCurveEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro X d gamma I Pi L R H C P N
    rfl
  · rfl

end BEDC.Derived.RectifiableCurveUp.TasteGate
