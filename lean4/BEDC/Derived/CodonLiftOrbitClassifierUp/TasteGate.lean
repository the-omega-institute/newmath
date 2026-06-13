import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CodonLiftOrbitClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CodonLiftOrbitClassifierUp : Type where
  | mk (A E Gamma T B K H C P N : BHist) : CodonLiftOrbitClassifierUp
  deriving DecidableEq

def codonLiftOrbitClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: codonLiftOrbitClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: codonLiftOrbitClassifierEncodeBHist h

def codonLiftOrbitClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (codonLiftOrbitClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (codonLiftOrbitClassifierDecodeBHist tail)

private theorem codonLiftOrbitClassifier_decode_encode :
    ∀ h : BHist,
      codonLiftOrbitClassifierDecodeBHist (codonLiftOrbitClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def codonLiftOrbitClassifierToEventFlow : CodonLiftOrbitClassifierUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CodonLiftOrbitClassifierUp.mk A E Gamma T B K H C P N =>
      [codonLiftOrbitClassifierEncodeBHist A,
        codonLiftOrbitClassifierEncodeBHist E,
        codonLiftOrbitClassifierEncodeBHist Gamma,
        codonLiftOrbitClassifierEncodeBHist T,
        codonLiftOrbitClassifierEncodeBHist B,
        codonLiftOrbitClassifierEncodeBHist K,
        codonLiftOrbitClassifierEncodeBHist H,
        codonLiftOrbitClassifierEncodeBHist C,
        codonLiftOrbitClassifierEncodeBHist P,
        codonLiftOrbitClassifierEncodeBHist N]

def codonLiftOrbitClassifierFromEventFlow :
    EventFlow → Option CodonLiftOrbitClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | A :: E :: Gamma :: T :: B :: K :: H :: C :: P :: N :: [] =>
      some
        (CodonLiftOrbitClassifierUp.mk
          (codonLiftOrbitClassifierDecodeBHist A)
          (codonLiftOrbitClassifierDecodeBHist E)
          (codonLiftOrbitClassifierDecodeBHist Gamma)
          (codonLiftOrbitClassifierDecodeBHist T)
          (codonLiftOrbitClassifierDecodeBHist B)
          (codonLiftOrbitClassifierDecodeBHist K)
          (codonLiftOrbitClassifierDecodeBHist H)
          (codonLiftOrbitClassifierDecodeBHist C)
          (codonLiftOrbitClassifierDecodeBHist P)
          (codonLiftOrbitClassifierDecodeBHist N))
  | _ => none

private theorem codonLiftOrbitClassifier_round_trip :
    ∀ x : CodonLiftOrbitClassifierUp,
      codonLiftOrbitClassifierFromEventFlow (codonLiftOrbitClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A E Gamma T B K H C P N =>
      simp only [codonLiftOrbitClassifierToEventFlow, codonLiftOrbitClassifierFromEventFlow,
        codonLiftOrbitClassifier_decode_encode]

private theorem codonLiftOrbitClassifierToEventFlow_injective
    {x y : CodonLiftOrbitClassifierUp} :
    codonLiftOrbitClassifierToEventFlow x = codonLiftOrbitClassifierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hx :
      codonLiftOrbitClassifierFromEventFlow (codonLiftOrbitClassifierToEventFlow x) =
        some x :=
    codonLiftOrbitClassifier_round_trip x
  have hy :
      codonLiftOrbitClassifierFromEventFlow (codonLiftOrbitClassifierToEventFlow y) =
        some y :=
    codonLiftOrbitClassifier_round_trip y
  have hflow :
      codonLiftOrbitClassifierFromEventFlow (codonLiftOrbitClassifierToEventFlow x) =
        codonLiftOrbitClassifierFromEventFlow (codonLiftOrbitClassifierToEventFlow y) :=
    congrArg codonLiftOrbitClassifierFromEventFlow hxy
  have hsome : some x = some y := Eq.trans hx.symm (Eq.trans hflow hy)
  cases hsome
  rfl

instance codonLiftOrbitClassifierBHistCarrier :
    BHistCarrier CodonLiftOrbitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := codonLiftOrbitClassifierToEventFlow
  fromEventFlow := codonLiftOrbitClassifierFromEventFlow

instance codonLiftOrbitClassifierChapterTasteGate :
    ChapterTasteGate CodonLiftOrbitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      codonLiftOrbitClassifierFromEventFlow (codonLiftOrbitClassifierToEventFlow x) =
        some x
    exact codonLiftOrbitClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (codonLiftOrbitClassifierToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CodonLiftOrbitClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  codonLiftOrbitClassifierChapterTasteGate

end BEDC.Derived.CodonLiftOrbitClassifierUp
