import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductBoundaryUp : Type where
  | mk (A B WA WB D M K R E H C P N : BHist) : CauchyProductBoundaryUp
  deriving DecidableEq

def cauchyProductBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductBoundaryEncodeBHist h

def cauchyProductBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductBoundaryDecodeBHist tail)

private theorem CauchyProductBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyProductBoundaryFields : CauchyProductBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductBoundaryUp.mk A B WA WB D M K R E H C P N =>
      [A, B, WA, WB, D, M, K, R, E, H, C, P, N]

def cauchyProductBoundaryToEventFlow : CauchyProductBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyProductBoundaryFields x).map cauchyProductBoundaryEncodeBHist

private def cauchyProductBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductBoundaryEventAtDefault index rest

def cauchyProductBoundaryFromEventFlow (ef : EventFlow) :
    Option CauchyProductBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductBoundaryUp.mk
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 0 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 1 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 2 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 3 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 4 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 5 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 6 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 7 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 8 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 9 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 10 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 11 ef))
      (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEventAtDefault 12 ef)))

private theorem CauchyProductBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyProductBoundaryUp,
      cauchyProductBoundaryFromEventFlow (cauchyProductBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B WA WB D M K R E H C P N =>
      change
        some
            (CauchyProductBoundaryUp.mk
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist A))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist B))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist WA))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist WB))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist D))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist M))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist K))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist R))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist E))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist H))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist C))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist P))
              (cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist N))) =
          some (CauchyProductBoundaryUp.mk A B WA WB D M K R E H C P N)
      rw [CauchyProductBoundaryTasteGate_single_carrier_alignment_decode A,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode B,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode WA,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode WB,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode D,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode M,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode K,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode R,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode E,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode H,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode C,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode P,
        CauchyProductBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem CauchyProductBoundaryTasteGate_single_carrier_alignment_injective
    {x y : CauchyProductBoundaryUp} :
    cauchyProductBoundaryToEventFlow x = cauchyProductBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductBoundaryFromEventFlow (cauchyProductBoundaryToEventFlow x) =
        cauchyProductBoundaryFromEventFlow (cauchyProductBoundaryToEventFlow y) :=
    congrArg cauchyProductBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyProductBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyProductBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyProductBoundaryBHistCarrier :
    BHistCarrier CauchyProductBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductBoundaryToEventFlow
  fromEventFlow := cauchyProductBoundaryFromEventFlow

instance cauchyProductBoundaryChapterTasteGate :
    ChapterTasteGate CauchyProductBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductBoundaryFromEventFlow (cauchyProductBoundaryToEventFlow x) = some x
    exact CauchyProductBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyProductBoundaryTasteGate_single_carrier_alignment_injective heq)

theorem CauchyProductBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyProductBoundaryDecodeBHist (cauchyProductBoundaryEncodeBHist h) = h) ∧
      (∀ x : CauchyProductBoundaryUp,
        cauchyProductBoundaryFromEventFlow (cauchyProductBoundaryToEventFlow x) = some x) ∧
        (∀ x y : CauchyProductBoundaryUp,
          cauchyProductBoundaryToEventFlow x = cauchyProductBoundaryToEventFlow y → x = y) ∧
          cauchyProductBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨CauchyProductBoundaryTasteGate_single_carrier_alignment_decode,
      CauchyProductBoundaryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyProductBoundaryTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyProductBoundaryUp
