import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterCriterionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterCriterionUp : Type where
  | mk (B K M U W R D E H C P N : BHist) : CauchyFilterCriterionUp
  deriving DecidableEq

def cauchyFilterCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterCriterionEncodeBHist h

def cauchyFilterCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterCriterionDecodeBHist tail)

private theorem CauchyFilterCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterCriterionFields : CauchyFilterCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterCriterionUp.mk B K M U W R D E H C P N => [B, K, M, U, W, R, D, E, H, C, P, N]

def cauchyFilterCriterionToEventFlow : CauchyFilterCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterCriterionFields x).map cauchyFilterCriterionEncodeBHist

private def cauchyFilterCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterCriterionEventAt index rest

def cauchyFilterCriterionFromEventFlow : EventFlow → Option CauchyFilterCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | _0 :: _1 :: _2 :: _3 :: _4 :: _5 :: _6 :: _7 :: _8 :: _9 :: _10 :: _11 :: [] =>
        some
          (CauchyFilterCriterionUp.mk
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 0 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 1 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 2 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 3 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 4 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 5 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 6 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 7 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 8 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 9 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 10 ef))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 11 ef)))
    | _ => none

private theorem CauchyFilterCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterCriterionUp,
      cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B K M U W R D E H C P N =>
      change
        some
          (CauchyFilterCriterionUp.mk
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist B))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist K))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist M))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist U))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist W))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist R))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist D))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist E))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist H))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist C))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist P))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist N))) =
          some (CauchyFilterCriterionUp.mk B K M U W R D E H C P N)
      rw [CauchyFilterCriterionTasteGate_single_carrier_alignment_decode B,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode K,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode M,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode U,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode W,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode R,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode D,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode E,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode H,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode C,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode P,
        CauchyFilterCriterionTasteGate_single_carrier_alignment_decode N]

private theorem CauchyFilterCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterCriterionUp} :
    cauchyFilterCriterionToEventFlow x = cauchyFilterCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) =
        cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow y) :=
    congrArg cauchyFilterCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyFilterCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyFilterCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterCriterionBHistCarrier : BHistCarrier CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterCriterionToEventFlow
  fromEventFlow := cauchyFilterCriterionFromEventFlow

instance cauchyFilterCriterionChapterTasteGate : ChapterTasteGate CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x
    exact CauchyFilterCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyFilterCriterionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyFilterCriterionUp) ∧
      (∀ h : BHist, cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyFilterCriterionUp,
        cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x) ∧
      (∀ x y : CauchyFilterCriterionUp,
        cauchyFilterCriterionToEventFlow x = cauchyFilterCriterionToEventFlow y → x = y) ∧
      cauchyFilterCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cauchyFilterCriterionChapterTasteGate⟩
  constructor
  · exact CauchyFilterCriterionTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyFilterCriterionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y
    exact CauchyFilterCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
  · rfl

end BEDC.Derived.CauchyFilterCriterionUp.TasteGate
