import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealComparisonModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealComparisonModulusUp : Type where
  | mk (B A R S D M H C P N : BHist) : BishopRealComparisonModulusUp
  deriving DecidableEq

def bishopRealComparisonModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealComparisonModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealComparisonModulusEncodeBHist h

def bishopRealComparisonModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealComparisonModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealComparisonModulusDecodeBHist tail)

private theorem BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealComparisonModulusFields : BishopRealComparisonModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealComparisonModulusUp.mk B A R S D M H C P N => [B, A, R, S, D, M, H, C, P, N]

def bishopRealComparisonModulusToEventFlow : BishopRealComparisonModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealComparisonModulusFields x).map bishopRealComparisonModulusEncodeBHist

private def bishopRealComparisonModulusEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealComparisonModulusEventAtDefault index rest

def bishopRealComparisonModulusFromEventFlow (ef : EventFlow) :
    Option BishopRealComparisonModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealComparisonModulusUp.mk
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 0 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 1 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 2 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 3 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 4 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 5 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 6 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 7 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 8 ef))
      (bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEventAtDefault 9 ef)))

private theorem BishopRealComparisonModulusTasteGate_single_carrier_alignment_round_trip
    (x : BishopRealComparisonModulusUp) :
    bishopRealComparisonModulusFromEventFlow (bishopRealComparisonModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B A R S D M H C P N =>
      change
        some
          (BishopRealComparisonModulusUp.mk
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist B))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist A))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist R))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist S))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist D))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist M))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist H))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist C))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist P))
            (bishopRealComparisonModulusDecodeBHist
              (bishopRealComparisonModulusEncodeBHist N))) =
          some (BishopRealComparisonModulusUp.mk B A R S D M H C P N)
      rw [BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode B,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode A,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode R,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode S,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode D,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode M,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode H,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode C,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode P,
        BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode N]

private theorem BishopRealComparisonModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealComparisonModulusUp} :
    bishopRealComparisonModulusToEventFlow x = bishopRealComparisonModulusToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealComparisonModulusFromEventFlow
          (bishopRealComparisonModulusToEventFlow x) =
        bishopRealComparisonModulusFromEventFlow
          (bishopRealComparisonModulusToEventFlow y) :=
    congrArg bishopRealComparisonModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealComparisonModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealComparisonModulusTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRealComparisonModulusBHistCarrier :
    BHistCarrier BishopRealComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealComparisonModulusToEventFlow
  fromEventFlow := bishopRealComparisonModulusFromEventFlow

instance bishopRealComparisonModulusChapterTasteGate :
    ChapterTasteGate BishopRealComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRealComparisonModulusFromEventFlow
          (bishopRealComparisonModulusToEventFlow x) =
        some x
    exact BishopRealComparisonModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealComparisonModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopRealComparisonModulusTasteGate_single_carrier_alignment :
    (forall h : BHist,
      bishopRealComparisonModulusDecodeBHist (bishopRealComparisonModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopRealComparisonModulusUp) ∧
        Nonempty (ChapterTasteGate BishopRealComparisonModulusUp) ∧
          bishopRealComparisonModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨BishopRealComparisonModulusTasteGate_single_carrier_alignment_decode,
      ⟨⟨bishopRealComparisonModulusBHistCarrier⟩,
        ⟨⟨bishopRealComparisonModulusChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.BishopRealComparisonModulusUp
