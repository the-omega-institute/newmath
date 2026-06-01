import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyInterleavingCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyInterleavingCriterionUp : Type where
  | mk (S0 S1 D0 D1 T W Q E H C P N : BHist) : CauchyInterleavingCriterionUp
  deriving DecidableEq

def cauchyInterleavingCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyInterleavingCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyInterleavingCriterionEncodeBHist h

def cauchyInterleavingCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyInterleavingCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyInterleavingCriterionDecodeBHist tail)

private theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyInterleavingCriterionFields : CauchyInterleavingCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyInterleavingCriterionUp.mk S0 S1 D0 D1 T W Q E H C P N =>
      [S0, S1, D0, D1, T, W, Q, E, H, C, P, N]

def cauchyInterleavingCriterionToEventFlow : CauchyInterleavingCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyInterleavingCriterionFields x).map cauchyInterleavingCriterionEncodeBHist

private def cauchyInterleavingCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyInterleavingCriterionEventAtDefault index rest

def cauchyInterleavingCriterionFromEventFlow
    (ef : EventFlow) : Option CauchyInterleavingCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyInterleavingCriterionUp.mk
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 0 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 1 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 2 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 3 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 4 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 5 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 6 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 7 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 8 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 9 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 10 ef))
      (cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEventAtDefault 11 ef)))

private theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyInterleavingCriterionUp,
      cauchyInterleavingCriterionFromEventFlow
        (cauchyInterleavingCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 D0 D1 T W Q E H C P N =>
      change
        some
          (CauchyInterleavingCriterionUp.mk
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist S0))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist S1))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist D0))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist D1))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist T))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist W))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist Q))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist E))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist H))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist C))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist P))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist N))) =
          some (CauchyInterleavingCriterionUp.mk S0 S1 D0 D1 T W Q E H C P N)
      rw [CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode S0,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode S1,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode D0,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode D1,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode T,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode W,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode Q,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode E,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode H,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode C,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode P,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode N]

private theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyInterleavingCriterionUp} :
    cauchyInterleavingCriterionToEventFlow x =
      cauchyInterleavingCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyInterleavingCriterionFromEventFlow (cauchyInterleavingCriterionToEventFlow x) =
        cauchyInterleavingCriterionFromEventFlow (cauchyInterleavingCriterionToEventFlow y) :=
    congrArg cauchyInterleavingCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyInterleavingCriterionBHistCarrier :
    BHistCarrier CauchyInterleavingCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyInterleavingCriterionToEventFlow
  fromEventFlow := cauchyInterleavingCriterionFromEventFlow

instance cauchyInterleavingCriterionChapterTasteGate :
    ChapterTasteGate CauchyInterleavingCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyInterleavingCriterionFromEventFlow
          (cauchyInterleavingCriterionToEventFlow x) =
        some x
    exact CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyInterleavingCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyInterleavingCriterionDecodeBHist
        (cauchyInterleavingCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyInterleavingCriterionUp,
        cauchyInterleavingCriterionFromEventFlow
            (cauchyInterleavingCriterionToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyInterleavingCriterionUp,
          cauchyInterleavingCriterionToEventFlow x =
            cauchyInterleavingCriterionToEventFlow y → x = y) ∧
          cauchyInterleavingCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode,
      CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyInterleavingCriterionUp
