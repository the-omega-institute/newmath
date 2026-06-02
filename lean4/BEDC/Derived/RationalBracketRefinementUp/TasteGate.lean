import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalBracketRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalBracketRefinementUp : Type where
  | mk (B epsilon L U L' U' W G A E H C P N : BHist) : RationalBracketRefinementUp
  deriving DecidableEq

def rationalBracketRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalBracketRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalBracketRefinementEncodeBHist h

def rationalBracketRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalBracketRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalBracketRefinementDecodeBHist tail)

private theorem RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RationalBracketRefinementTasteGate_single_carrier_alignment_fields :
    RationalBracketRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalBracketRefinementUp.mk B epsilon L U L' U' W G A E H C P N =>
      [B, epsilon, L, U, L', U', W, G, A, E, H, C, P, N]

def rationalBracketRefinementToEventFlow : RationalBracketRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (RationalBracketRefinementTasteGate_single_carrier_alignment_fields x).map
        rationalBracketRefinementEncodeBHist

private def rationalBracketRefinementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalBracketRefinementEventAtDefault index rest

def rationalBracketRefinementFromEventFlow
    (ef : EventFlow) : Option RationalBracketRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalBracketRefinementUp.mk
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 0 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 1 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 2 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 3 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 4 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 5 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 6 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 7 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 8 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 9 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 10 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 11 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 12 ef))
      (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEventAtDefault 13 ef)))

private theorem RationalBracketRefinementTasteGate_single_carrier_alignment_round_trip
    (x : RationalBracketRefinementUp) :
    rationalBracketRefinementFromEventFlow (rationalBracketRefinementToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B epsilon L U L' U' W G A E H C P N =>
      change
        some
          (RationalBracketRefinementUp.mk
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist B))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist epsilon))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist L))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist U))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist L'))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist U'))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist W))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist G))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist A))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist E))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist H))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist C))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist P))
            (rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist N))) =
          some (RationalBracketRefinementUp.mk B epsilon L U L' U' W G A E H C P N)
      rw [RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode B,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode epsilon,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode L,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode U,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode L',
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode U',
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode W,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode G,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode A,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode E,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode H,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode C,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode P,
        RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode N]

private theorem RationalBracketRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalBracketRefinementUp} :
    rationalBracketRefinementToEventFlow x = rationalBracketRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalBracketRefinementFromEventFlow (rationalBracketRefinementToEventFlow x) =
        rationalBracketRefinementFromEventFlow (rationalBracketRefinementToEventFlow y) :=
    congrArg rationalBracketRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RationalBracketRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalBracketRefinementTasteGate_single_carrier_alignment_round_trip y)))

instance rationalBracketRefinementBHistCarrier :
    BHistCarrier RationalBracketRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalBracketRefinementToEventFlow
  fromEventFlow := rationalBracketRefinementFromEventFlow

instance rationalBracketRefinementChapterTasteGate :
    ChapterTasteGate RationalBracketRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalBracketRefinementFromEventFlow (rationalBracketRefinementToEventFlow x) =
      some x
    exact RationalBracketRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RationalBracketRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RationalBracketRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalBracketRefinementChapterTasteGate

theorem RationalBracketRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalBracketRefinementDecodeBHist (rationalBracketRefinementEncodeBHist h) = h) ∧
      RationalBracketRefinementTasteGate_single_carrier_alignment_fields
          (RationalBracketRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RationalBracketRefinementTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.RationalBracketRefinementUp
