import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailIntersectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailIntersectionUp : Type where
  | mk (X Y W0 W1 I D R E H C P N : BHist) : CauchyTailIntersectionUp
  deriving DecidableEq

def cauchyTailIntersectionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailIntersectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailIntersectionEncodeBHist h

def cauchyTailIntersectionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailIntersectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailIntersectionDecodeBHist tail)

private theorem cauchyTailIntersectionDecode_encode :
    ∀ h : BHist,
      cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailIntersectionToEventFlow : CauchyTailIntersectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailIntersectionUp.mk X Y W0 W1 I D R E H C P N =>
      [cauchyTailIntersectionEncodeBHist X,
        cauchyTailIntersectionEncodeBHist Y,
        cauchyTailIntersectionEncodeBHist W0,
        cauchyTailIntersectionEncodeBHist W1,
        cauchyTailIntersectionEncodeBHist I,
        cauchyTailIntersectionEncodeBHist D,
        cauchyTailIntersectionEncodeBHist R,
        cauchyTailIntersectionEncodeBHist E,
        cauchyTailIntersectionEncodeBHist H,
        cauchyTailIntersectionEncodeBHist C,
        cauchyTailIntersectionEncodeBHist P,
        cauchyTailIntersectionEncodeBHist N]

def cauchyTailIntersectionFromEventFlow : EventFlow -> Option CauchyTailIntersectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: Y :: W0 :: W1 :: I :: D :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (CauchyTailIntersectionUp.mk
          (cauchyTailIntersectionDecodeBHist X)
          (cauchyTailIntersectionDecodeBHist Y)
          (cauchyTailIntersectionDecodeBHist W0)
          (cauchyTailIntersectionDecodeBHist W1)
          (cauchyTailIntersectionDecodeBHist I)
          (cauchyTailIntersectionDecodeBHist D)
          (cauchyTailIntersectionDecodeBHist R)
          (cauchyTailIntersectionDecodeBHist E)
          (cauchyTailIntersectionDecodeBHist H)
          (cauchyTailIntersectionDecodeBHist C)
          (cauchyTailIntersectionDecodeBHist P)
          (cauchyTailIntersectionDecodeBHist N))
  | _ => none

private theorem cauchyTailIntersection_round_trip :
    ∀ x : CauchyTailIntersectionUp,
      cauchyTailIntersectionFromEventFlow (cauchyTailIntersectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W0 W1 I D R E H C P N =>
      change
        some
            (CauchyTailIntersectionUp.mk
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist X))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist Y))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist W0))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist W1))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist I))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist D))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist R))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist E))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist H))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist C))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist P))
              (cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist N))) =
          some (CauchyTailIntersectionUp.mk X Y W0 W1 I D R E H C P N)
      rw [cauchyTailIntersectionDecode_encode X, cauchyTailIntersectionDecode_encode Y,
        cauchyTailIntersectionDecode_encode W0, cauchyTailIntersectionDecode_encode W1,
        cauchyTailIntersectionDecode_encode I, cauchyTailIntersectionDecode_encode D,
        cauchyTailIntersectionDecode_encode R, cauchyTailIntersectionDecode_encode E,
        cauchyTailIntersectionDecode_encode H, cauchyTailIntersectionDecode_encode C,
        cauchyTailIntersectionDecode_encode P, cauchyTailIntersectionDecode_encode N]

private theorem cauchyTailIntersectionToEventFlow_injective
    {x y : CauchyTailIntersectionUp} :
    cauchyTailIntersectionToEventFlow x = cauchyTailIntersectionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailIntersectionFromEventFlow (cauchyTailIntersectionToEventFlow x) =
        cauchyTailIntersectionFromEventFlow (cauchyTailIntersectionToEventFlow y) :=
    congrArg cauchyTailIntersectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailIntersection_round_trip x).symm
      (Eq.trans hread (cauchyTailIntersection_round_trip y)))

instance cauchyTailIntersectionBHistCarrier : BHistCarrier CauchyTailIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailIntersectionToEventFlow
  fromEventFlow := cauchyTailIntersectionFromEventFlow

instance cauchyTailIntersectionChapterTasteGate : ChapterTasteGate CauchyTailIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailIntersectionFromEventFlow (cauchyTailIntersectionToEventFlow x) = some x
    exact cauchyTailIntersection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailIntersectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyTailIntersectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailIntersectionChapterTasteGate

theorem CauchyTailIntersectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailIntersectionDecodeBHist (cauchyTailIntersectionEncodeBHist h) = h) ∧
      Nonempty CauchyTailIntersectionUp ∧
        cauchyTailIntersectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyTailIntersectionDecode_encode,
      ⟨CauchyTailIntersectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty⟩,
      rfl⟩

end BEDC.Derived.CauchyTailIntersectionUp
