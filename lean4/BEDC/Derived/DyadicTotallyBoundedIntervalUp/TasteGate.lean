import BEDC.Derived.DyadicTotallyBoundedIntervalUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicTotallyBoundedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def dyadicTotallyBoundedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicTotallyBoundedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicTotallyBoundedIntervalEncodeBHist h

def dyadicTotallyBoundedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicTotallyBoundedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicTotallyBoundedIntervalDecodeBHist tail)

private theorem dyadicTotallyBoundedIntervalDecode_encode :
    ∀ h : BHist,
      dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicTotallyBoundedIntervalToEventFlow :
    BEDC.Derived.DyadicTotallyBoundedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.DyadicTotallyBoundedIntervalUp.mk L U M Z rho F S R E H C P N =>
      [dyadicTotallyBoundedIntervalEncodeBHist L,
        dyadicTotallyBoundedIntervalEncodeBHist U,
        dyadicTotallyBoundedIntervalEncodeBHist M,
        dyadicTotallyBoundedIntervalEncodeBHist Z,
        dyadicTotallyBoundedIntervalEncodeBHist rho,
        dyadicTotallyBoundedIntervalEncodeBHist F,
        dyadicTotallyBoundedIntervalEncodeBHist S,
        dyadicTotallyBoundedIntervalEncodeBHist R,
        dyadicTotallyBoundedIntervalEncodeBHist E,
        dyadicTotallyBoundedIntervalEncodeBHist H,
        dyadicTotallyBoundedIntervalEncodeBHist C,
        dyadicTotallyBoundedIntervalEncodeBHist P,
        dyadicTotallyBoundedIntervalEncodeBHist N]

private def dyadicTotallyBoundedIntervalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicTotallyBoundedIntervalEventAt index rest

def dyadicTotallyBoundedIntervalFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.DyadicTotallyBoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.DyadicTotallyBoundedIntervalUp.mk
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 0 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 1 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 2 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 3 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 4 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 5 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 6 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 7 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 8 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 9 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 10 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 11 ef))
      (dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEventAt 12 ef)))

private theorem dyadicTotallyBoundedInterval_round_trip :
    ∀ x : BEDC.Derived.DyadicTotallyBoundedIntervalUp,
      dyadicTotallyBoundedIntervalFromEventFlow
        (dyadicTotallyBoundedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U M Z rho F S R E H C P N =>
      change
        some
          (BEDC.Derived.DyadicTotallyBoundedIntervalUp.mk
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist L))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist U))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist M))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist Z))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist rho))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist F))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist S))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist R))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist E))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist H))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist C))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist P))
            (dyadicTotallyBoundedIntervalDecodeBHist
              (dyadicTotallyBoundedIntervalEncodeBHist N))) =
          some (BEDC.Derived.DyadicTotallyBoundedIntervalUp.mk L U M Z rho F S R E H C P N)
      rw [dyadicTotallyBoundedIntervalDecode_encode L,
        dyadicTotallyBoundedIntervalDecode_encode U,
        dyadicTotallyBoundedIntervalDecode_encode M,
        dyadicTotallyBoundedIntervalDecode_encode Z,
        dyadicTotallyBoundedIntervalDecode_encode rho,
        dyadicTotallyBoundedIntervalDecode_encode F,
        dyadicTotallyBoundedIntervalDecode_encode S,
        dyadicTotallyBoundedIntervalDecode_encode R,
        dyadicTotallyBoundedIntervalDecode_encode E,
        dyadicTotallyBoundedIntervalDecode_encode H,
        dyadicTotallyBoundedIntervalDecode_encode C,
        dyadicTotallyBoundedIntervalDecode_encode P,
        dyadicTotallyBoundedIntervalDecode_encode N]

private theorem dyadicTotallyBoundedIntervalToEventFlow_injective
    {x y : BEDC.Derived.DyadicTotallyBoundedIntervalUp} :
    dyadicTotallyBoundedIntervalToEventFlow x =
      dyadicTotallyBoundedIntervalToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicTotallyBoundedIntervalFromEventFlow
          (dyadicTotallyBoundedIntervalToEventFlow x) =
        dyadicTotallyBoundedIntervalFromEventFlow
          (dyadicTotallyBoundedIntervalToEventFlow y) :=
    congrArg dyadicTotallyBoundedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicTotallyBoundedInterval_round_trip x).symm
      (Eq.trans hread (dyadicTotallyBoundedInterval_round_trip y)))

instance dyadicTotallyBoundedIntervalBHistCarrier :
    BHistCarrier BEDC.Derived.DyadicTotallyBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicTotallyBoundedIntervalToEventFlow
  fromEventFlow := dyadicTotallyBoundedIntervalFromEventFlow

instance dyadicTotallyBoundedIntervalChapterTasteGate :
    ChapterTasteGate BEDC.Derived.DyadicTotallyBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicTotallyBoundedIntervalFromEventFlow
        (dyadicTotallyBoundedIntervalToEventFlow x) = some x
    exact dyadicTotallyBoundedInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicTotallyBoundedIntervalToEventFlow_injective heq)

theorem DyadicTotallyBoundedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicTotallyBoundedIntervalDecodeBHist
        (dyadicTotallyBoundedIntervalEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.DyadicTotallyBoundedIntervalUp,
        dyadicTotallyBoundedIntervalFromEventFlow
          (dyadicTotallyBoundedIntervalToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.DyadicTotallyBoundedIntervalUp,
          dyadicTotallyBoundedIntervalToEventFlow x =
            dyadicTotallyBoundedIntervalToEventFlow y →
              x = y) ∧
          dyadicTotallyBoundedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨dyadicTotallyBoundedIntervalDecode_encode,
      dyadicTotallyBoundedInterval_round_trip,
      fun _ _ heq => dyadicTotallyBoundedIntervalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DyadicTotallyBoundedIntervalUp
