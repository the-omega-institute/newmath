import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteModulusCompactUniformEquicontinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteModulusCompactUniformEquicontinuityUp : Type where
  | mk (K F M U D S Q R H C P N : BHist) :
      FiniteModulusCompactUniformEquicontinuityUp
  deriving DecidableEq

def finiteModulusCompactUniformEquicontinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteModulusCompactUniformEquicontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteModulusCompactUniformEquicontinuityEncodeBHist h

def finiteModulusCompactUniformEquicontinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (finiteModulusCompactUniformEquicontinuityDecodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (finiteModulusCompactUniformEquicontinuityDecodeBHist tail)

private theorem FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteModulusCompactUniformEquicontinuityToEventFlow :
    FiniteModulusCompactUniformEquicontinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteModulusCompactUniformEquicontinuityUp.mk K F M U D S Q R H C P N =>
      [finiteModulusCompactUniformEquicontinuityEncodeBHist K,
        finiteModulusCompactUniformEquicontinuityEncodeBHist F,
        finiteModulusCompactUniformEquicontinuityEncodeBHist M,
        finiteModulusCompactUniformEquicontinuityEncodeBHist U,
        finiteModulusCompactUniformEquicontinuityEncodeBHist D,
        finiteModulusCompactUniformEquicontinuityEncodeBHist S,
        finiteModulusCompactUniformEquicontinuityEncodeBHist Q,
        finiteModulusCompactUniformEquicontinuityEncodeBHist R,
        finiteModulusCompactUniformEquicontinuityEncodeBHist H,
        finiteModulusCompactUniformEquicontinuityEncodeBHist C,
        finiteModulusCompactUniformEquicontinuityEncodeBHist P,
        finiteModulusCompactUniformEquicontinuityEncodeBHist N]

private def finiteModulusCompactUniformEquicontinuityEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteModulusCompactUniformEquicontinuityEventAtDefault index rest

def finiteModulusCompactUniformEquicontinuityFromEventFlow
    (ef : EventFlow) : Option FiniteModulusCompactUniformEquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteModulusCompactUniformEquicontinuityUp.mk
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 0 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 1 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 2 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 3 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 4 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 5 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 6 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 7 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 8 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 9 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 10 ef))
      (finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEventAtDefault 11 ef)))

private theorem FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_round_trip
    (x : FiniteModulusCompactUniformEquicontinuityUp) :
    finiteModulusCompactUniformEquicontinuityFromEventFlow
        (finiteModulusCompactUniformEquicontinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F M U D S Q R H C P N =>
      change
        some
          (FiniteModulusCompactUniformEquicontinuityUp.mk
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist K))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist F))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist M))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist U))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist D))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist S))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist Q))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist R))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist H))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist C))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist P))
            (finiteModulusCompactUniformEquicontinuityDecodeBHist
              (finiteModulusCompactUniformEquicontinuityEncodeBHist N))) =
          some (FiniteModulusCompactUniformEquicontinuityUp.mk K F M U D S Q R H C P N)
      rw [FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode K,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode F,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode M,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode U,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode D,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode S,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode Q,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode R,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode H,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode C,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode P,
        FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteModulusCompactUniformEquicontinuityUp} :
    finiteModulusCompactUniformEquicontinuityToEventFlow x =
      finiteModulusCompactUniformEquicontinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteModulusCompactUniformEquicontinuityFromEventFlow
          (finiteModulusCompactUniformEquicontinuityToEventFlow x) =
        finiteModulusCompactUniformEquicontinuityFromEventFlow
          (finiteModulusCompactUniformEquicontinuityToEventFlow y) :=
    congrArg finiteModulusCompactUniformEquicontinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_round_trip y)))

instance finiteModulusCompactUniformEquicontinuityBHistCarrier :
    BHistCarrier FiniteModulusCompactUniformEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteModulusCompactUniformEquicontinuityToEventFlow
  fromEventFlow := finiteModulusCompactUniformEquicontinuityFromEventFlow

instance finiteModulusCompactUniformEquicontinuityChapterTasteGate :
    ChapterTasteGate FiniteModulusCompactUniformEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteModulusCompactUniformEquicontinuityFromEventFlow
          (finiteModulusCompactUniformEquicontinuityToEventFlow x) = some x
    exact
      FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteModulusCompactUniformEquicontinuityDecodeBHist
        (finiteModulusCompactUniformEquicontinuityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteModulusCompactUniformEquicontinuityUp) ∧
        Nonempty (ChapterTasteGate FiniteModulusCompactUniformEquicontinuityUp) ∧
          finiteModulusCompactUniformEquicontinuityEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteModulusCompactUniformEquicontinuityTasteGate_single_carrier_alignment_decode_encode,
      ⟨finiteModulusCompactUniformEquicontinuityBHistCarrier⟩,
      ⟨finiteModulusCompactUniformEquicontinuityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteModulusCompactUniformEquicontinuityUp
