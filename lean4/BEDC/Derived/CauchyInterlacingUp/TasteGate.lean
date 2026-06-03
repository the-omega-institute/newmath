import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyInterlacingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyInterlacingUp : Type where
  | mk (A B W D T R H C P N : BHist) : CauchyInterlacingUp

def cauchyInterlacingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyInterlacingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyInterlacingEncodeBHist h

def cauchyInterlacingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyInterlacingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyInterlacingDecodeBHist tail)

private theorem CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyInterlacingFields : CauchyInterlacingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyInterlacingUp.mk A B W D T R H C P N => [A, B, W, D, T, R, H, C, P, N]

def cauchyInterlacingToEventFlow : CauchyInterlacingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyInterlacingFields x).map cauchyInterlacingEncodeBHist

private def cauchyInterlacingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyInterlacingEventAt index rest

def cauchyInterlacingFromEventFlow (ef : EventFlow) : Option CauchyInterlacingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyInterlacingUp.mk
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 0 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 1 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 2 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 3 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 4 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 5 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 6 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 7 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 8 ef))
      (cauchyInterlacingDecodeBHist (cauchyInterlacingEventAt 9 ef)))

private theorem CauchyInterlacingTasteGate_single_carrier_alignment_round_trip
    (x : CauchyInterlacingUp) :
    cauchyInterlacingFromEventFlow (cauchyInterlacingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B W D T R H C P N =>
      change
        some
          (CauchyInterlacingUp.mk
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist A))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist B))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist W))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist D))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist T))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist R))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist H))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist C))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist P))
            (cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist N))) =
          some (CauchyInterlacingUp.mk A B W D T R H C P N)
      rw [CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode A,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode B,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode W,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode D,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode T,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode R,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode H,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode C,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode P,
        CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode N]

private theorem cauchyInterlacingToEventFlow_injective {x y : CauchyInterlacingUp} :
    cauchyInterlacingToEventFlow x = cauchyInterlacingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyInterlacingFromEventFlow (cauchyInterlacingToEventFlow x) =
        cauchyInterlacingFromEventFlow (cauchyInterlacingToEventFlow y) :=
    congrArg cauchyInterlacingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyInterlacingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyInterlacingTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyInterlacingBHistCarrier : BHistCarrier CauchyInterlacingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyInterlacingToEventFlow
  fromEventFlow := cauchyInterlacingFromEventFlow

instance cauchyInterlacingChapterTasteGate : ChapterTasteGate CauchyInterlacingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyInterlacingFromEventFlow (cauchyInterlacingToEventFlow x) = some x
    exact CauchyInterlacingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyInterlacingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyInterlacingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyInterlacingChapterTasteGate

theorem CauchyInterlacingTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyInterlacingDecodeBHist (cauchyInterlacingEncodeBHist h) = h) ∧
      (∀ x : CauchyInterlacingUp,
        cauchyInterlacingFromEventFlow (cauchyInterlacingToEventFlow x) = some x) ∧
        (∀ x y : CauchyInterlacingUp,
          cauchyInterlacingToEventFlow x = cauchyInterlacingToEventFlow y → x = y) ∧
          cauchyInterlacingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyInterlacingTasteGate_single_carrier_alignment_decode_encode,
      CauchyInterlacingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => cauchyInterlacingToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyInterlacingUp
