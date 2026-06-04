import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletenessDiagonalSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletenessDiagonalSelectorUp : Type where
  | mk (R E T S Q D A H C P N : BHist) : RealCompletenessDiagonalSelectorUp
  deriving DecidableEq

def realCompletenessDiagonalSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletenessDiagonalSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletenessDiagonalSelectorEncodeBHist h

def realCompletenessDiagonalSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletenessDiagonalSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletenessDiagonalSelectorDecodeBHist tail)

private theorem realCompletenessDiagonalSelectorDecode_encode_bhist :
    ∀ h : BHist,
      realCompletenessDiagonalSelectorDecodeBHist
          (realCompletenessDiagonalSelectorEncodeBHist h) =
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

def realCompletenessDiagonalSelectorToEventFlow :
    RealCompletenessDiagonalSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletenessDiagonalSelectorUp.mk R E T S Q D A H C P N =>
      [realCompletenessDiagonalSelectorEncodeBHist R,
        realCompletenessDiagonalSelectorEncodeBHist E,
        realCompletenessDiagonalSelectorEncodeBHist T,
        realCompletenessDiagonalSelectorEncodeBHist S,
        realCompletenessDiagonalSelectorEncodeBHist Q,
        realCompletenessDiagonalSelectorEncodeBHist D,
        realCompletenessDiagonalSelectorEncodeBHist A,
        realCompletenessDiagonalSelectorEncodeBHist H,
        realCompletenessDiagonalSelectorEncodeBHist C,
        realCompletenessDiagonalSelectorEncodeBHist P,
        realCompletenessDiagonalSelectorEncodeBHist N]

private def realCompletenessDiagonalSelectorEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realCompletenessDiagonalSelectorEventAtDefault index rest

def realCompletenessDiagonalSelectorFromEventFlow
    (ef : EventFlow) : Option RealCompletenessDiagonalSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCompletenessDiagonalSelectorUp.mk
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 0 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 1 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 2 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 3 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 4 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 5 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 6 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 7 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 8 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 9 ef))
      (realCompletenessDiagonalSelectorDecodeBHist
        (realCompletenessDiagonalSelectorEventAtDefault 10 ef)))

private theorem realCompletenessDiagonalSelector_round_trip :
    ∀ x : RealCompletenessDiagonalSelectorUp,
      realCompletenessDiagonalSelectorFromEventFlow
          (realCompletenessDiagonalSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R E T S Q D A H C P N =>
      change
        some
          (RealCompletenessDiagonalSelectorUp.mk
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist R))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist E))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist T))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist S))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist Q))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist D))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist A))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist H))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist C))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist P))
            (realCompletenessDiagonalSelectorDecodeBHist
              (realCompletenessDiagonalSelectorEncodeBHist N))) =
          some (RealCompletenessDiagonalSelectorUp.mk R E T S Q D A H C P N)
      rw [realCompletenessDiagonalSelectorDecode_encode_bhist R,
        realCompletenessDiagonalSelectorDecode_encode_bhist E,
        realCompletenessDiagonalSelectorDecode_encode_bhist T,
        realCompletenessDiagonalSelectorDecode_encode_bhist S,
        realCompletenessDiagonalSelectorDecode_encode_bhist Q,
        realCompletenessDiagonalSelectorDecode_encode_bhist D,
        realCompletenessDiagonalSelectorDecode_encode_bhist A,
        realCompletenessDiagonalSelectorDecode_encode_bhist H,
        realCompletenessDiagonalSelectorDecode_encode_bhist C,
        realCompletenessDiagonalSelectorDecode_encode_bhist P,
        realCompletenessDiagonalSelectorDecode_encode_bhist N]

private theorem realCompletenessDiagonalSelectorToEventFlow_injective
    {x y : RealCompletenessDiagonalSelectorUp} :
    realCompletenessDiagonalSelectorToEventFlow x =
        realCompletenessDiagonalSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletenessDiagonalSelectorFromEventFlow
          (realCompletenessDiagonalSelectorToEventFlow x) =
        realCompletenessDiagonalSelectorFromEventFlow
          (realCompletenessDiagonalSelectorToEventFlow y) :=
    congrArg realCompletenessDiagonalSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletenessDiagonalSelector_round_trip x).symm
      (Eq.trans hread (realCompletenessDiagonalSelector_round_trip y)))

instance realCompletenessDiagonalSelectorBHistCarrier :
    BHistCarrier RealCompletenessDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletenessDiagonalSelectorToEventFlow
  fromEventFlow := realCompletenessDiagonalSelectorFromEventFlow

instance realCompletenessDiagonalSelectorChapterTasteGate :
    ChapterTasteGate RealCompletenessDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletenessDiagonalSelectorFromEventFlow
          (realCompletenessDiagonalSelectorToEventFlow x) =
        some x
    exact realCompletenessDiagonalSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletenessDiagonalSelectorToEventFlow_injective heq)

theorem RealCompletenessDiagonalSelectorTasteGate_single_carrier_alignment :
    (forall h : BHist,
      realCompletenessDiagonalSelectorDecodeBHist
          (realCompletenessDiagonalSelectorEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RealCompletenessDiagonalSelectorUp) ∧
        Nonempty (ChapterTasteGate RealCompletenessDiagonalSelectorUp) ∧
          realCompletenessDiagonalSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realCompletenessDiagonalSelectorDecode_encode_bhist,
      ⟨realCompletenessDiagonalSelectorBHistCarrier⟩,
      ⟨realCompletenessDiagonalSelectorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealCompletenessDiagonalSelectorUp
