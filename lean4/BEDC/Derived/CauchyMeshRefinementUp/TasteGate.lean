import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMeshRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMeshRefinementUp : Type where
  | mk (Q0 Q1 D0 D1 J S R T E H C P N : BHist) : CauchyMeshRefinementUp
  deriving DecidableEq

def cauchyMeshRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMeshRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMeshRefinementEncodeBHist h

def cauchyMeshRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMeshRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMeshRefinementDecodeBHist tail)

private theorem CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyMeshRefinementFields : CauchyMeshRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMeshRefinementUp.mk Q0 Q1 D0 D1 J S R T E H C P N =>
      [Q0, Q1, D0, D1, J, S, R, T, E, H, C, P, N]

def cauchyMeshRefinementToEventFlow : CauchyMeshRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyMeshRefinementFields x).map cauchyMeshRefinementEncodeBHist

private def CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt index rest

def cauchyMeshRefinementFromEventFlow (ef : EventFlow) :
    Option CauchyMeshRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyMeshRefinementUp.mk
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 7 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 8 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 9 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 10 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 11 ef))
      (cauchyMeshRefinementDecodeBHist
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_eventAt 12 ef)))

private theorem CauchyMeshRefinementTasteGate_single_carrier_alignment_round_trip
    (x : CauchyMeshRefinementUp) :
    cauchyMeshRefinementFromEventFlow (cauchyMeshRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q0 Q1 D0 D1 J S R T E H C P N =>
      change
        some
          (CauchyMeshRefinementUp.mk
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist Q0))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist Q1))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist D0))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist D1))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist J))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist S))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist R))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist T))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist E))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist H))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist C))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist P))
            (cauchyMeshRefinementDecodeBHist (cauchyMeshRefinementEncodeBHist N))) =
          some (CauchyMeshRefinementUp.mk Q0 Q1 D0 D1 J S R T E H C P N)
      rw [CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode Q0,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode Q1,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode D0,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode D1,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode J,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode S,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode R,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode T,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode E,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode H,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode C,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode P,
        CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyMeshRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyMeshRefinementUp} :
    cauchyMeshRefinementToEventFlow x = cauchyMeshRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMeshRefinementFromEventFlow (cauchyMeshRefinementToEventFlow x) =
        cauchyMeshRefinementFromEventFlow (cauchyMeshRefinementToEventFlow y) :=
    congrArg cauchyMeshRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyMeshRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyMeshRefinementTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyMeshRefinementBHistCarrier :
    BHistCarrier CauchyMeshRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMeshRefinementToEventFlow
  fromEventFlow := cauchyMeshRefinementFromEventFlow

instance cauchyMeshRefinementChapterTasteGate :
    ChapterTasteGate CauchyMeshRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyMeshRefinementFromEventFlow (cauchyMeshRefinementToEventFlow x) =
      some x
    exact CauchyMeshRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyMeshRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyMeshRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyMeshRefinementDecodeBHist
        (cauchyMeshRefinementEncodeBHist h) = h) ∧
      (∀ x : CauchyMeshRefinementUp,
        cauchyMeshRefinementFromEventFlow
          (cauchyMeshRefinementToEventFlow x) = some x) ∧
      (∀ x y : CauchyMeshRefinementUp,
        cauchyMeshRefinementToEventFlow x =
          cauchyMeshRefinementToEventFlow y -> x = y) ∧
      cauchyMeshRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyMeshRefinementTasteGate_single_carrier_alignment_decode_encode,
      CauchyMeshRefinementTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyMeshRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyMeshRefinementUp
