import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectorTriangleHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectorTriangleHandoffUp : Type where
  | mk (F T U K S D R E J C P N : BHist) :
      CauchyCompletionReflectorTriangleHandoffUp
  deriving DecidableEq

def cauchyCompletionReflectorTriangleHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectorTriangleHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectorTriangleHandoffEncodeBHist h

def cauchyCompletionReflectorTriangleHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectorTriangleHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectorTriangleHandoffDecodeBHist tail)

private theorem CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectorTriangleHandoffFields :
    CauchyCompletionReflectorTriangleHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectorTriangleHandoffUp.mk F T U K S D R E J C P N =>
      [F, T, U, K, S, D, R, E, J, C, P, N]

def cauchyCompletionReflectorTriangleHandoffToEventFlow :
    CauchyCompletionReflectorTriangleHandoffUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionReflectorTriangleHandoffFields x).map
      cauchyCompletionReflectorTriangleHandoffEncodeBHist

private def cauchyCompletionReflectorTriangleHandoffEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionReflectorTriangleHandoffEventAtDefault index rest

def cauchyCompletionReflectorTriangleHandoffFromEventFlow :
    EventFlow → Option CauchyCompletionReflectorTriangleHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionReflectorTriangleHandoffUp.mk
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 0 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 1 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 2 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 3 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 4 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 5 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 6 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 7 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 8 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 9 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 10 ef))
        (cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEventAtDefault 11 ef)))

private theorem CauchyCompletionReflectorTriangleHandoffTasteGate_round_trip
    (x : CauchyCompletionReflectorTriangleHandoffUp) :
    cauchyCompletionReflectorTriangleHandoffFromEventFlow
        (cauchyCompletionReflectorTriangleHandoffToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F T U K S D R E J C P N =>
      change
        some
          (CauchyCompletionReflectorTriangleHandoffUp.mk
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist F))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist T))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist U))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist K))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist S))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist D))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist R))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist E))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist J))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist C))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist P))
            (cauchyCompletionReflectorTriangleHandoffDecodeBHist
              (cauchyCompletionReflectorTriangleHandoffEncodeBHist N))) =
          some (CauchyCompletionReflectorTriangleHandoffUp.mk F T U K S D R E J C P N)
      rw [CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode F,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode T,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode U,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode K,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode S,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode D,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode R,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode E,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode J,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode C,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode P,
        CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode N]

private theorem CauchyCompletionReflectorTriangleHandoffTasteGate_toEventFlow_injective
    {x y : CauchyCompletionReflectorTriangleHandoffUp} :
    cauchyCompletionReflectorTriangleHandoffToEventFlow x =
        cauchyCompletionReflectorTriangleHandoffToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          cauchyCompletionReflectorTriangleHandoffFromEventFlow
            (cauchyCompletionReflectorTriangleHandoffToEventFlow x) :=
        (CauchyCompletionReflectorTriangleHandoffTasteGate_round_trip x).symm
      _ =
          cauchyCompletionReflectorTriangleHandoffFromEventFlow
            (cauchyCompletionReflectorTriangleHandoffToEventFlow y) :=
        congrArg cauchyCompletionReflectorTriangleHandoffFromEventFlow hxy
      _ = some y := CauchyCompletionReflectorTriangleHandoffTasteGate_round_trip y
  exact Option.some.inj optionEq

instance cauchyCompletionReflectorTriangleHandoffBHistCarrier :
    BHistCarrier CauchyCompletionReflectorTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectorTriangleHandoffToEventFlow
  fromEventFlow := cauchyCompletionReflectorTriangleHandoffFromEventFlow

instance cauchyCompletionReflectorTriangleHandoffChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectorTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectorTriangleHandoffFromEventFlow
          (cauchyCompletionReflectorTriangleHandoffToEventFlow x) =
        some x
    exact CauchyCompletionReflectorTriangleHandoffTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionReflectorTriangleHandoffTasteGate_toEventFlow_injective heq)

theorem CauchyCompletionReflectorTriangleHandoffTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionReflectorTriangleHandoffDecodeBHist
          (cauchyCompletionReflectorTriangleHandoffEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CauchyCompletionReflectorTriangleHandoffUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionReflectorTriangleHandoffUp) ∧
          cauchyCompletionReflectorTriangleHandoffEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionReflectorTriangleHandoffTasteGate_decode_encode,
      ⟨cauchyCompletionReflectorTriangleHandoffBHistCarrier⟩,
      ⟨cauchyCompletionReflectorTriangleHandoffChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionReflectorTriangleHandoffUp
