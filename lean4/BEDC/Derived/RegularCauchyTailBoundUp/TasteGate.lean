import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailBoundUp : Type where
  | mk (S R D N T0 H C P L : BHist) : RegularCauchyTailBoundUp
  deriving DecidableEq

def regularCauchyTailBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailBoundEncodeBHist h

def regularCauchyTailBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailBoundDecodeBHist tail)

private theorem regularCauchyTailBound_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailBoundFields : RegularCauchyTailBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailBoundUp.mk S R D N T0 H C P L => [S, R, D, N, T0, H, C, P, L]

def regularCauchyTailBoundToEventFlow : RegularCauchyTailBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailBoundFields x).map regularCauchyTailBoundEncodeBHist

private def regularCauchyTailBoundEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailBoundEventAtDefault index rest

def regularCauchyTailBoundFromEventFlow :
    EventFlow → Option RegularCauchyTailBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyTailBoundUp.mk
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 0 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 1 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 2 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 3 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 4 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 5 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 6 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 7 ef))
        (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEventAtDefault 8 ef)))

private theorem regularCauchyTailBound_round_trip :
    ∀ x : RegularCauchyTailBoundUp,
      regularCauchyTailBoundFromEventFlow (regularCauchyTailBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D N T0 H C P L =>
      change
        some
            (RegularCauchyTailBoundUp.mk
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist S))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist R))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist D))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist N))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist T0))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist H))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist C))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist P))
              (regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist L))) =
          some (RegularCauchyTailBoundUp.mk S R D N T0 H C P L)
      rw [regularCauchyTailBound_decode_encode_bhist S,
        regularCauchyTailBound_decode_encode_bhist R,
        regularCauchyTailBound_decode_encode_bhist D,
        regularCauchyTailBound_decode_encode_bhist N,
        regularCauchyTailBound_decode_encode_bhist T0,
        regularCauchyTailBound_decode_encode_bhist H,
        regularCauchyTailBound_decode_encode_bhist C,
        regularCauchyTailBound_decode_encode_bhist P,
        regularCauchyTailBound_decode_encode_bhist L]

private theorem regularCauchyTailBoundToEventFlow_injective
    {x y : RegularCauchyTailBoundUp} :
    regularCauchyTailBoundToEventFlow x = regularCauchyTailBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailBoundFromEventFlow (regularCauchyTailBoundToEventFlow x) =
        regularCauchyTailBoundFromEventFlow (regularCauchyTailBoundToEventFlow y) :=
    congrArg regularCauchyTailBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailBound_round_trip x).symm
      (Eq.trans hread (regularCauchyTailBound_round_trip y)))

instance regularCauchyTailBoundBHistCarrier :
    BHistCarrier RegularCauchyTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailBoundToEventFlow
  fromEventFlow := regularCauchyTailBoundFromEventFlow

instance regularCauchyTailBoundChapterTasteGate :
    ChapterTasteGate RegularCauchyTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTailBoundFromEventFlow (regularCauchyTailBoundToEventFlow x) = some x
    exact regularCauchyTailBound_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailBoundToEventFlow_injective heq)

theorem RegularCauchyTailBoundTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyTailBoundDecodeBHist (regularCauchyTailBoundEncodeBHist h) = h) ∧
      (forall x : RegularCauchyTailBoundUp,
        regularCauchyTailBoundFromEventFlow (regularCauchyTailBoundToEventFlow x) = some x) ∧
        (forall x y : RegularCauchyTailBoundUp,
          regularCauchyTailBoundToEventFlow x = regularCauchyTailBoundToEventFlow y ->
            x = y) ∧
          regularCauchyTailBoundEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyTailBound_decode_encode_bhist,
      regularCauchyTailBound_round_trip,
      (fun _ _ heq => regularCauchyTailBoundToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyTailBoundUp
