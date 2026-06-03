import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationIntegralBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationIntegralBoundUp : Type where
  | mk (M D I B W R E H C P N : BHist) : CauchyCondensationIntegralBoundUp
  deriving DecidableEq

def cauchyCondensationIntegralBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationIntegralBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationIntegralBoundEncodeBHist h

def cauchyCondensationIntegralBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationIntegralBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationIntegralBoundDecodeBHist tail)

private theorem cauchyCondensationIntegralBound_decode_encode_bhist :
    ∀ h : BHist, cauchyCondensationIntegralBoundDecodeBHist
      (cauchyCondensationIntegralBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCondensationIntegralBoundFields :
    CauchyCondensationIntegralBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationIntegralBoundUp.mk M D I B W R E H C P N =>
      [M, D, I, B, W, R, E, H, C, P, N]

def cauchyCondensationIntegralBoundToEventFlow :
    CauchyCondensationIntegralBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCondensationIntegralBoundFields x).map
      cauchyCondensationIntegralBoundEncodeBHist

private def cauchyCondensationIntegralBoundEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCondensationIntegralBoundEventAtDefault index rest

def cauchyCondensationIntegralBoundFromEventFlow :
    EventFlow → Option CauchyCondensationIntegralBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCondensationIntegralBoundUp.mk
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 0 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 1 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 2 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 3 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 4 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 5 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 6 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 7 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 8 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 9 ef))
        (cauchyCondensationIntegralBoundDecodeBHist
          (cauchyCondensationIntegralBoundEventAtDefault 10 ef)))

private theorem cauchyCondensationIntegralBound_round_trip :
    ∀ x : CauchyCondensationIntegralBoundUp,
      cauchyCondensationIntegralBoundFromEventFlow
        (cauchyCondensationIntegralBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D I B W R E H C P N =>
      change
        some
          (CauchyCondensationIntegralBoundUp.mk
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist M))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist D))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist I))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist B))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist W))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist R))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist E))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist H))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist C))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist P))
            (cauchyCondensationIntegralBoundDecodeBHist
              (cauchyCondensationIntegralBoundEncodeBHist N))) =
          some (CauchyCondensationIntegralBoundUp.mk M D I B W R E H C P N)
      rw [cauchyCondensationIntegralBound_decode_encode_bhist M,
        cauchyCondensationIntegralBound_decode_encode_bhist D,
        cauchyCondensationIntegralBound_decode_encode_bhist I,
        cauchyCondensationIntegralBound_decode_encode_bhist B,
        cauchyCondensationIntegralBound_decode_encode_bhist W,
        cauchyCondensationIntegralBound_decode_encode_bhist R,
        cauchyCondensationIntegralBound_decode_encode_bhist E,
        cauchyCondensationIntegralBound_decode_encode_bhist H,
        cauchyCondensationIntegralBound_decode_encode_bhist C,
        cauchyCondensationIntegralBound_decode_encode_bhist P,
        cauchyCondensationIntegralBound_decode_encode_bhist N]

private theorem cauchyCondensationIntegralBoundToEventFlow_injective
    {x y : CauchyCondensationIntegralBoundUp} :
    cauchyCondensationIntegralBoundToEventFlow x =
      cauchyCondensationIntegralBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCondensationIntegralBoundFromEventFlow
          (cauchyCondensationIntegralBoundToEventFlow x) =
        cauchyCondensationIntegralBoundFromEventFlow
          (cauchyCondensationIntegralBoundToEventFlow y) :=
    congrArg cauchyCondensationIntegralBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCondensationIntegralBound_round_trip x).symm
      (Eq.trans hread (cauchyCondensationIntegralBound_round_trip y)))

instance cauchyCondensationIntegralBoundBHistCarrier :
    BHistCarrier CauchyCondensationIntegralBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationIntegralBoundToEventFlow
  fromEventFlow := cauchyCondensationIntegralBoundFromEventFlow

instance cauchyCondensationIntegralBoundChapterTasteGate :
    ChapterTasteGate CauchyCondensationIntegralBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCondensationIntegralBoundFromEventFlow
      (cauchyCondensationIntegralBoundToEventFlow x) = some x
    exact cauchyCondensationIntegralBound_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCondensationIntegralBoundToEventFlow_injective heq)

theorem CauchyCondensationIntegralBoundTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCondensationIntegralBoundDecodeBHist
      (cauchyCondensationIntegralBoundEncodeBHist h) = h) ∧
      (∀ x : CauchyCondensationIntegralBoundUp,
        cauchyCondensationIntegralBoundFromEventFlow
          (cauchyCondensationIntegralBoundToEventFlow x) = some x) ∧
        (∀ x y : CauchyCondensationIntegralBoundUp,
          cauchyCondensationIntegralBoundToEventFlow x =
            cauchyCondensationIntegralBoundToEventFlow y → x = y) ∧
          cauchyCondensationIntegralBoundEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyCondensationIntegralBound_decode_encode_bhist,
      cauchyCondensationIntegralBound_round_trip,
      (fun _ _ heq => cauchyCondensationIntegralBoundToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCondensationIntegralBoundUp
