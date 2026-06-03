import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyComparisonUp : Type where
  | mk (S Q M D R E H C P N : BHist) : BishopCauchyComparisonUp
  deriving DecidableEq

def bishopCauchyComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyComparisonEncodeBHist h

def bishopCauchyComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyComparisonDecodeBHist tail)

private theorem bishopCauchyComparison_decode_encode :
    ∀ h : BHist,
      bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyComparisonFields : BishopCauchyComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyComparisonUp.mk S Q M D R E H C P N =>
      [S, Q, M, D, R, E, H, C, P, N]

def bishopCauchyComparisonToEventFlow : BishopCauchyComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCauchyComparisonFields x).map bishopCauchyComparisonEncodeBHist

private def bishopCauchyComparisonEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyComparisonEventAtDefault index rest

def bishopCauchyComparisonFromEventFlow
    (ef : EventFlow) : Option BishopCauchyComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyComparisonUp.mk
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 0 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 1 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 2 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 3 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 4 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 5 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 6 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 7 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 8 ef))
      (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEventAtDefault 9 ef)))

private theorem bishopCauchyComparison_round_trip :
    ∀ x : BishopCauchyComparisonUp,
      bishopCauchyComparisonFromEventFlow (bishopCauchyComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q M D R E H C P N =>
      change
        some
          (BishopCauchyComparisonUp.mk
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist S))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist Q))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist M))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist D))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist R))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist E))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist H))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist C))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist P))
            (bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist N))) =
          some (BishopCauchyComparisonUp.mk S Q M D R E H C P N)
      rw [bishopCauchyComparison_decode_encode S,
        bishopCauchyComparison_decode_encode Q,
        bishopCauchyComparison_decode_encode M,
        bishopCauchyComparison_decode_encode D,
        bishopCauchyComparison_decode_encode R,
        bishopCauchyComparison_decode_encode E,
        bishopCauchyComparison_decode_encode H,
        bishopCauchyComparison_decode_encode C,
        bishopCauchyComparison_decode_encode P,
        bishopCauchyComparison_decode_encode N]

private theorem bishopCauchyComparisonToEventFlow_injective
    {x y : BishopCauchyComparisonUp} :
    bishopCauchyComparisonToEventFlow x = bishopCauchyComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyComparisonFromEventFlow (bishopCauchyComparisonToEventFlow x) =
        bishopCauchyComparisonFromEventFlow (bishopCauchyComparisonToEventFlow y) :=
    congrArg bishopCauchyComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (bishopCauchyComparison_round_trip x).symm
      (Eq.trans hread (bishopCauchyComparison_round_trip y)))

instance bishopCauchyComparisonBHistCarrier :
    BHistCarrier BishopCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyComparisonToEventFlow
  fromEventFlow := bishopCauchyComparisonFromEventFlow

instance bishopCauchyComparisonChapterTasteGate :
    ChapterTasteGate BishopCauchyComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCauchyComparisonFromEventFlow (bishopCauchyComparisonToEventFlow x) =
      some x
    exact bishopCauchyComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCauchyComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyComparisonChapterTasteGate

theorem BishopCauchyComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopCauchyComparisonDecodeBHist (bishopCauchyComparisonEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopCauchyComparisonUp) ∧
      Nonempty (ChapterTasteGate BishopCauchyComparisonUp) ∧
      bishopCauchyComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bishopCauchyComparison_decode_encode,
      ⟨bishopCauchyComparisonBHistCarrier⟩,
      ⟨bishopCauchyComparisonChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopCauchyComparisonUp
