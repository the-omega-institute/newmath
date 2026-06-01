import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalApartnessModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalApartnessModulusUp : Type where
  | mk (I A G T S R D E H C P N : BHist) : BishopIntervalApartnessModulusUp
  deriving DecidableEq

def bishopIntervalApartnessModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalApartnessModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalApartnessModulusEncodeBHist h

def bishopIntervalApartnessModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalApartnessModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalApartnessModulusDecodeBHist tail)

private theorem BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopIntervalApartnessModulusFields :
    BishopIntervalApartnessModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalApartnessModulusUp.mk I A G T S R D E H C P N =>
      [I, A, G, T, S, R, D, E, H, C, P, N]

def bishopIntervalApartnessModulusToEventFlow :
    BishopIntervalApartnessModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopIntervalApartnessModulusFields x).map
    bishopIntervalApartnessModulusEncodeBHist

private def bishopIntervalApartnessModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopIntervalApartnessModulusEventAtDefault index rest

def bishopIntervalApartnessModulusFromEventFlow
    (ef : EventFlow) : Option BishopIntervalApartnessModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopIntervalApartnessModulusUp.mk
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 0 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 1 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 2 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 3 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 4 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 5 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 6 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 7 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 8 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 9 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 10 ef))
      (bishopIntervalApartnessModulusDecodeBHist
        (bishopIntervalApartnessModulusEventAtDefault 11 ef)))

private theorem BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopIntervalApartnessModulusUp,
      bishopIntervalApartnessModulusFromEventFlow
        (bishopIntervalApartnessModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I A G T S R D E H C P N =>
      change
        some
          (BishopIntervalApartnessModulusUp.mk
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist I))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist A))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist G))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist T))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist S))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist R))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist D))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist E))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist H))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist C))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist P))
            (bishopIntervalApartnessModulusDecodeBHist
              (bishopIntervalApartnessModulusEncodeBHist N))) =
          some (BishopIntervalApartnessModulusUp.mk I A G T S R D E H C P N)
      rw [BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode I,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode A,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode G,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode T,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode S,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode R,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode D,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode E,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode H,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode C,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode P,
        BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode N]

private theorem BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopIntervalApartnessModulusUp} :
    bishopIntervalApartnessModulusToEventFlow x =
      bishopIntervalApartnessModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalApartnessModulusFromEventFlow
          (bishopIntervalApartnessModulusToEventFlow x) =
        bishopIntervalApartnessModulusFromEventFlow
          (bishopIntervalApartnessModulusToEventFlow y) :=
    congrArg bishopIntervalApartnessModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_round_trip y)))

instance bishopIntervalApartnessModulusBHistCarrier :
    BHistCarrier BishopIntervalApartnessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalApartnessModulusToEventFlow
  fromEventFlow := bishopIntervalApartnessModulusFromEventFlow

instance bishopIntervalApartnessModulusChapterTasteGate :
    ChapterTasteGate BishopIntervalApartnessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopIntervalApartnessModulusFromEventFlow
        (bishopIntervalApartnessModulusToEventFlow x) = some x
    exact BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem BishopIntervalApartnessModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopIntervalApartnessModulusDecodeBHist
          (bishopIntervalApartnessModulusEncodeBHist h) = h) ∧
      (∀ x : BishopIntervalApartnessModulusUp,
        bishopIntervalApartnessModulusFromEventFlow
          (bishopIntervalApartnessModulusToEventFlow x) = some x) ∧
        bishopIntervalApartnessModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_decode,
      BishopIntervalApartnessModulusTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.BishopIntervalApartnessModulusUp
