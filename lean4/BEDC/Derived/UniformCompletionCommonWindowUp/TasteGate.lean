import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionCommonWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionCommonWindowUp : Type where
  | mk (U E S R D L F H C P N : BHist) : UniformCompletionCommonWindowUp
  deriving DecidableEq

def uniformCompletionCommonWindowEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionCommonWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionCommonWindowEncodeBHist h

def uniformCompletionCommonWindowDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionCommonWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionCommonWindowDecodeBHist tail)

private theorem uniformCompletionCommonWindow_decode_encode_bhist :
    forall h : BHist,
      uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionCommonWindowFields :
    UniformCompletionCommonWindowUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionCommonWindowUp.mk U E S R D L F H C P N =>
      [U, E, S, R, D, L, F, H, C, P, N]

def uniformCompletionCommonWindowToEventFlow :
    UniformCompletionCommonWindowUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (uniformCompletionCommonWindowFields x).map
      uniformCompletionCommonWindowEncodeBHist

private def uniformCompletionCommonWindowEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformCompletionCommonWindowEventAtDefault index rest

def uniformCompletionCommonWindowFromEventFlow
    (ef : EventFlow) : Option UniformCompletionCommonWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCompletionCommonWindowUp.mk
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 0 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 1 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 2 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 3 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 4 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 5 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 6 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 7 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 8 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 9 ef))
      (uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEventAtDefault 10 ef)))

private theorem uniformCompletionCommonWindow_round_trip :
    forall x : UniformCompletionCommonWindowUp,
      uniformCompletionCommonWindowFromEventFlow
        (uniformCompletionCommonWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U E S R D L F H C P N =>
      change
        some
          (UniformCompletionCommonWindowUp.mk
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist U))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist E))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist S))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist R))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist D))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist L))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist F))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist H))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist C))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist P))
            (uniformCompletionCommonWindowDecodeBHist
              (uniformCompletionCommonWindowEncodeBHist N))) =
          some (UniformCompletionCommonWindowUp.mk U E S R D L F H C P N)
      rw [uniformCompletionCommonWindow_decode_encode_bhist U,
        uniformCompletionCommonWindow_decode_encode_bhist E,
        uniformCompletionCommonWindow_decode_encode_bhist S,
        uniformCompletionCommonWindow_decode_encode_bhist R,
        uniformCompletionCommonWindow_decode_encode_bhist D,
        uniformCompletionCommonWindow_decode_encode_bhist L,
        uniformCompletionCommonWindow_decode_encode_bhist F,
        uniformCompletionCommonWindow_decode_encode_bhist H,
        uniformCompletionCommonWindow_decode_encode_bhist C,
        uniformCompletionCommonWindow_decode_encode_bhist P,
        uniformCompletionCommonWindow_decode_encode_bhist N]

private theorem uniformCompletionCommonWindowToEventFlow_injective
    {x y : UniformCompletionCommonWindowUp} :
    uniformCompletionCommonWindowToEventFlow x =
      uniformCompletionCommonWindowToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCompletionCommonWindowFromEventFlow
          (uniformCompletionCommonWindowToEventFlow x) =
        uniformCompletionCommonWindowFromEventFlow
          (uniformCompletionCommonWindowToEventFlow y) :=
    congrArg uniformCompletionCommonWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCompletionCommonWindow_round_trip x).symm
      (Eq.trans hread (uniformCompletionCommonWindow_round_trip y)))

instance uniformCompletionCommonWindowBHistCarrier :
    BHistCarrier UniformCompletionCommonWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionCommonWindowToEventFlow
  fromEventFlow := uniformCompletionCommonWindowFromEventFlow

instance uniformCompletionCommonWindowChapterTasteGate :
    ChapterTasteGate UniformCompletionCommonWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCompletionCommonWindowFromEventFlow
        (uniformCompletionCommonWindowToEventFlow x) = some x
    exact uniformCompletionCommonWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCompletionCommonWindowToEventFlow_injective heq)

theorem UniformCompletionCommonWindowTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformCompletionCommonWindowDecodeBHist
        (uniformCompletionCommonWindowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformCompletionCommonWindowUp) ∧
        Nonempty (ChapterTasteGate UniformCompletionCommonWindowUp) ∧
          uniformCompletionCommonWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨uniformCompletionCommonWindow_decode_encode_bhist,
      ⟨uniformCompletionCommonWindowBHistCarrier⟩,
      ⟨uniformCompletionCommonWindowChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.UniformCompletionCommonWindowUp
