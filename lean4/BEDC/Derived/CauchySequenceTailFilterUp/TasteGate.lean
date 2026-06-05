import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceTailFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceTailFilterUp : Type where
  | mk (S B F C D Q R E H K P N : BHist) : CauchySequenceTailFilterUp
  deriving DecidableEq

def cauchySequenceTailFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceTailFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceTailFilterEncodeBHist h

def cauchySequenceTailFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceTailFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceTailFilterDecodeBHist tail)

private theorem CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceTailFilterFields : CauchySequenceTailFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceTailFilterUp.mk S B F C D Q R E H K P N =>
      [S, B, F, C, D, Q, R, E, H, K, P, N]

def cauchySequenceTailFilterToEventFlow : CauchySequenceTailFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchySequenceTailFilterFields x).map cauchySequenceTailFilterEncodeBHist

private def cauchySequenceTailFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceTailFilterEventAtDefault index rest

def cauchySequenceTailFilterFromEventFlow
    (ef : EventFlow) : Option CauchySequenceTailFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySequenceTailFilterUp.mk
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 0 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 1 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 2 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 3 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 4 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 5 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 6 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 7 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 8 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 9 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 10 ef))
      (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEventAtDefault 11 ef)))

private theorem CauchySequenceTailFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchySequenceTailFilterUp,
      cauchySequenceTailFilterFromEventFlow (cauchySequenceTailFilterToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B F C D Q R E H K P N =>
      change
        some
          (CauchySequenceTailFilterUp.mk
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist S))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist B))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist F))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist C))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist D))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist Q))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist R))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist E))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist H))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist K))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist P))
            (cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist N))) =
          some (CauchySequenceTailFilterUp.mk S B F C D Q R E H K P N)
      rw [CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode S,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode B,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode F,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode C,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode D,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode Q,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode R,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode E,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode H,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode K,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode P,
        CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode N]

private theorem CauchySequenceTailFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySequenceTailFilterUp} :
    cauchySequenceTailFilterToEventFlow x = cauchySequenceTailFilterToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceTailFilterFromEventFlow (cauchySequenceTailFilterToEventFlow x) =
        cauchySequenceTailFilterFromEventFlow (cauchySequenceTailFilterToEventFlow y) :=
    congrArg cauchySequenceTailFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchySequenceTailFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySequenceTailFilterTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySequenceTailFilterBHistCarrier :
    BHistCarrier CauchySequenceTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceTailFilterToEventFlow
  fromEventFlow := cauchySequenceTailFilterFromEventFlow

instance cauchySequenceTailFilterChapterTasteGate :
    ChapterTasteGate CauchySequenceTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequenceTailFilterFromEventFlow (cauchySequenceTailFilterToEventFlow x) =
        some x
    exact CauchySequenceTailFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchySequenceTailFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySequenceTailFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceTailFilterChapterTasteGate

theorem CauchySequenceTailFilterTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchySequenceTailFilterDecodeBHist (cauchySequenceTailFilterEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchySequenceTailFilterUp) ∧
        Nonempty (ChapterTasteGate CauchySequenceTailFilterUp) ∧
          cauchySequenceTailFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchySequenceTailFilterTasteGate_single_carrier_alignment_decode,
      ⟨cauchySequenceTailFilterBHistCarrier⟩,
      ⟨cauchySequenceTailFilterChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchySequenceTailFilterUp
