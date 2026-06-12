import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySchwarzEqualityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySchwarzEqualityUp : Type where
  | mk (V X Y I A B C L D Q S R H T P N : BHist) : CauchySchwarzEqualityUp
  deriving DecidableEq

def cauchySchwarzEqualityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySchwarzEqualityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySchwarzEqualityEncodeBHist h

def cauchySchwarzEqualityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySchwarzEqualityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySchwarzEqualityDecodeBHist tail)

private theorem CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySchwarzEqualityFields : CauchySchwarzEqualityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySchwarzEqualityUp.mk V X Y I A B C L D Q S R H T P N =>
      [V, X, Y, I, A, B, C, L, D, Q, S, R, H, T, P, N]

def cauchySchwarzEqualityToEventFlow : CauchySchwarzEqualityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySchwarzEqualityFields x).map cauchySchwarzEqualityEncodeBHist

private def cauchySchwarzEqualityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySchwarzEqualityEventAtDefault index rest

def cauchySchwarzEqualityFromEventFlow
    (ef : EventFlow) : Option CauchySchwarzEqualityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySchwarzEqualityUp.mk
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 0 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 1 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 2 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 3 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 4 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 5 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 6 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 7 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 8 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 9 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 10 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 11 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 12 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 13 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 14 ef))
      (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEventAtDefault 15 ef)))

private theorem CauchySchwarzEqualityTasteGate_single_carrier_alignment_round_trip
    (x : CauchySchwarzEqualityUp) :
    cauchySchwarzEqualityFromEventFlow (cauchySchwarzEqualityToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk V X Y I A B C L D Q S R H T P N =>
      change
        some
          (CauchySchwarzEqualityUp.mk
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist V))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist X))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist Y))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist I))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist A))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist B))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist C))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist L))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist D))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist Q))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist S))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist R))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist H))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist T))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist P))
            (cauchySchwarzEqualityDecodeBHist (cauchySchwarzEqualityEncodeBHist N))) =
          some (CauchySchwarzEqualityUp.mk V X Y I A B C L D Q S R H T P N)
      rw [CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode V,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode X,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode Y,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode I,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode A,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode B,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode C,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode L,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode D,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode Q,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode S,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode R,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode H,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode T,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode P,
        CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode N]

private theorem CauchySchwarzEqualityTasteGate_single_carrier_alignment_injective
    {x y : CauchySchwarzEqualityUp} :
    cauchySchwarzEqualityToEventFlow x = cauchySchwarzEqualityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySchwarzEqualityFromEventFlow (cauchySchwarzEqualityToEventFlow x) =
        cauchySchwarzEqualityFromEventFlow (cauchySchwarzEqualityToEventFlow y) :=
    congrArg cauchySchwarzEqualityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySchwarzEqualityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySchwarzEqualityTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySchwarzEqualityBHistCarrier :
    BHistCarrier CauchySchwarzEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySchwarzEqualityToEventFlow
  fromEventFlow := cauchySchwarzEqualityFromEventFlow

instance cauchySchwarzEqualityChapterTasteGate :
    ChapterTasteGate CauchySchwarzEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySchwarzEqualityFromEventFlow (cauchySchwarzEqualityToEventFlow x) =
      some x
    exact CauchySchwarzEqualityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySchwarzEqualityTasteGate_single_carrier_alignment_injective heq)

theorem CauchySchwarzEqualityTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier CauchySchwarzEqualityUp,
      Nonempty (@ChapterTasteGate CauchySchwarzEqualityUp carrier)) ∧
      (∀ h : BHist,
        cauchySchwarzEqualityDecodeBHist
          (cauchySchwarzEqualityEncodeBHist h) = h) ∧
      (∀ x : CauchySchwarzEqualityUp,
        cauchySchwarzEqualityFromEventFlow
          (cauchySchwarzEqualityToEventFlow x) = some x) ∧
      cauchySchwarzEqualityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchySchwarzEqualityBHistCarrier, ⟨cauchySchwarzEqualityChapterTasteGate⟩⟩,
      CauchySchwarzEqualityTasteGate_single_carrier_alignment_decode,
      CauchySchwarzEqualityTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchySchwarzEqualityUp
