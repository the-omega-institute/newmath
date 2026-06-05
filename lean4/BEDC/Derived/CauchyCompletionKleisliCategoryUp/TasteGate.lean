import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionKleisliCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionKleisliCategoryUp : Type where
  | mk (O U A B E R H C P N : BHist) : CauchyCompletionKleisliCategoryUp

def cauchyCompletionKleisliCategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionKleisliCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionKleisliCategoryEncodeBHist h

def cauchyCompletionKleisliCategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionKleisliCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionKleisliCategoryDecodeBHist tail)

private theorem cauchyCompletionKleisliCategory_decode_encode :
    ∀ h : BHist,
      cauchyCompletionKleisliCategoryDecodeBHist
          (cauchyCompletionKleisliCategoryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionKleisliCategoryFields :
    CauchyCompletionKleisliCategoryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionKleisliCategoryUp.mk O U A B E R H C P N =>
      [O, U, A, B, E, R, H, C, P, N]

def cauchyCompletionKleisliCategoryToEventFlow :
    CauchyCompletionKleisliCategoryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCompletionKleisliCategoryFields x).map
    cauchyCompletionKleisliCategoryEncodeBHist

private def cauchyCompletionKleisliCategoryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionKleisliCategoryEventAtDefault index rest

def cauchyCompletionKleisliCategoryFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionKleisliCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionKleisliCategoryUp.mk
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 0 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 1 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 2 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 3 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 4 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 5 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 6 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 7 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 8 ef))
      (cauchyCompletionKleisliCategoryDecodeBHist
        (cauchyCompletionKleisliCategoryEventAtDefault 9 ef)))

private theorem cauchyCompletionKleisliCategory_round_trip :
    ∀ x : CauchyCompletionKleisliCategoryUp,
      cauchyCompletionKleisliCategoryFromEventFlow
          (cauchyCompletionKleisliCategoryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O U A B E R H C P N =>
      change
        some
          (CauchyCompletionKleisliCategoryUp.mk
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist O))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist U))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist A))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist B))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist E))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist R))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist H))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist C))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist P))
            (cauchyCompletionKleisliCategoryDecodeBHist
              (cauchyCompletionKleisliCategoryEncodeBHist N))) =
          some (CauchyCompletionKleisliCategoryUp.mk O U A B E R H C P N)
      rw [cauchyCompletionKleisliCategory_decode_encode O,
        cauchyCompletionKleisliCategory_decode_encode U,
        cauchyCompletionKleisliCategory_decode_encode A,
        cauchyCompletionKleisliCategory_decode_encode B,
        cauchyCompletionKleisliCategory_decode_encode E,
        cauchyCompletionKleisliCategory_decode_encode R,
        cauchyCompletionKleisliCategory_decode_encode H,
        cauchyCompletionKleisliCategory_decode_encode C,
        cauchyCompletionKleisliCategory_decode_encode P,
        cauchyCompletionKleisliCategory_decode_encode N]

private theorem cauchyCompletionKleisliCategoryToEventFlow_injective
    {x y : CauchyCompletionKleisliCategoryUp} :
    cauchyCompletionKleisliCategoryToEventFlow x =
      cauchyCompletionKleisliCategoryToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionKleisliCategoryFromEventFlow
          (cauchyCompletionKleisliCategoryToEventFlow x) =
        cauchyCompletionKleisliCategoryFromEventFlow
          (cauchyCompletionKleisliCategoryToEventFlow y) :=
    congrArg cauchyCompletionKleisliCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionKleisliCategory_round_trip x).symm
      (Eq.trans hread (cauchyCompletionKleisliCategory_round_trip y)))

instance cauchyCompletionKleisliCategoryBHistCarrier :
    BHistCarrier CauchyCompletionKleisliCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionKleisliCategoryToEventFlow
  fromEventFlow := cauchyCompletionKleisliCategoryFromEventFlow

instance cauchyCompletionKleisliCategoryChapterTasteGate :
    ChapterTasteGate CauchyCompletionKleisliCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionKleisliCategoryFromEventFlow
          (cauchyCompletionKleisliCategoryToEventFlow x) =
        some x
    exact cauchyCompletionKleisliCategory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionKleisliCategoryToEventFlow_injective heq)

theorem CauchyCompletionKleisliCategoryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionKleisliCategoryDecodeBHist
          (cauchyCompletionKleisliCategoryEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CauchyCompletionKleisliCategoryUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionKleisliCategoryUp) ∧
          cauchyCompletionKleisliCategoryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyCompletionKleisliCategory_decode_encode,
      ⟨cauchyCompletionKleisliCategoryBHistCarrier⟩,
      ⟨cauchyCompletionKleisliCategoryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionKleisliCategoryUp
