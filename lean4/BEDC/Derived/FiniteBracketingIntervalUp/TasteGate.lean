import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteBracketingIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteBracketingIntervalUp : Type where
  | mk (L U D W R E S H C P N : BHist) : FiniteBracketingIntervalUp
  deriving DecidableEq

def finiteBracketingIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteBracketingIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteBracketingIntervalEncodeBHist h

def finiteBracketingIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteBracketingIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteBracketingIntervalDecodeBHist tail)

private theorem finiteBracketingIntervalDecodeEncodeBHist :
    ∀ h : BHist,
      finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteBracketingIntervalFields : FiniteBracketingIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteBracketingIntervalUp.mk L U D W R E S H C P N =>
      [L, U, D, W, R, E, S, H, C, P, N]

def finiteBracketingIntervalToEventFlow : FiniteBracketingIntervalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteBracketingIntervalFields x).map finiteBracketingIntervalEncodeBHist

private def finiteBracketingIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteBracketingIntervalEventAtDefault index rest

def finiteBracketingIntervalFromEventFlow
    (ef : EventFlow) : Option FiniteBracketingIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteBracketingIntervalUp.mk
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 0 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 1 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 2 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 3 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 4 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 5 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 6 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 7 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 8 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 9 ef))
      (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEventAtDefault 10 ef)))

private theorem FiniteBracketingIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteBracketingIntervalUp,
      finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk L U D W R E S H C P N =>
      change
        some
          (FiniteBracketingIntervalUp.mk
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist L))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist U))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist D))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist W))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist R))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist E))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist S))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist H))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist C))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist P))
            (finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist N))) =
          some (FiniteBracketingIntervalUp.mk L U D W R E S H C P N)
      rw [finiteBracketingIntervalDecodeEncodeBHist L,
        finiteBracketingIntervalDecodeEncodeBHist U,
        finiteBracketingIntervalDecodeEncodeBHist D,
        finiteBracketingIntervalDecodeEncodeBHist W,
        finiteBracketingIntervalDecodeEncodeBHist R,
        finiteBracketingIntervalDecodeEncodeBHist E,
        finiteBracketingIntervalDecodeEncodeBHist S,
        finiteBracketingIntervalDecodeEncodeBHist H,
        finiteBracketingIntervalDecodeEncodeBHist C,
        finiteBracketingIntervalDecodeEncodeBHist P,
        finiteBracketingIntervalDecodeEncodeBHist N]

private theorem finiteBracketingIntervalToEventFlow_injective
    {x y : FiniteBracketingIntervalUp} :
    finiteBracketingIntervalToEventFlow x = finiteBracketingIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) =
        finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow y) :=
    congrArg finiteBracketingIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteBracketingIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteBracketingIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance finiteBracketingIntervalBHistCarrier :
    BHistCarrier FiniteBracketingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteBracketingIntervalToEventFlow
  fromEventFlow := finiteBracketingIntervalFromEventFlow

instance finiteBracketingIntervalChapterTasteGate :
    ChapterTasteGate FiniteBracketingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) =
      some x
    exact FiniteBracketingIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteBracketingIntervalToEventFlow_injective heq)

theorem FiniteBracketingIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteBracketingIntervalDecodeBHist (finiteBracketingIntervalEncodeBHist h) = h) ∧
      (∀ x : FiniteBracketingIntervalUp,
        finiteBracketingIntervalFromEventFlow (finiteBracketingIntervalToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteBracketingIntervalUp,
          finiteBracketingIntervalToEventFlow x =
            finiteBracketingIntervalToEventFlow y → x = y) ∧
          finiteBracketingIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteBracketingIntervalDecodeEncodeBHist,
      FiniteBracketingIntervalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => finiteBracketingIntervalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteBracketingIntervalUp
