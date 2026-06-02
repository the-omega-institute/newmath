import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetCompletionUp : Type where
  | mk (D W Q M U S R A H C P N : BHist) : CauchyNetCompletionUp
  deriving DecidableEq

def cauchyNetCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetCompletionEncodeBHist h

def cauchyNetCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetCompletionDecodeBHist tail)

private theorem CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNetCompletionFields : CauchyNetCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetCompletionUp.mk D W Q M U S R A H C P N => [D, W, Q, M, U, S, R, A, H, C, P, N]

def cauchyNetCompletionToEventFlow : CauchyNetCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyNetCompletionFields x).map cauchyNetCompletionEncodeBHist

private def cauchyNetCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyNetCompletionEventAt index rest

def cauchyNetCompletionFromEventFlow : EventFlow → Option CauchyNetCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (CauchyNetCompletionUp.mk
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 0 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 1 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 2 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 3 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 4 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 5 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 6 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 7 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 8 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 9 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 10 flow))
        (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEventAt 11 flow)))

private theorem CauchyNetCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyNetCompletionUp,
      cauchyNetCompletionFromEventFlow (cauchyNetCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q M U S R A H C P N =>
      change
        some
          (CauchyNetCompletionUp.mk
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist D))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist W))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist Q))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist M))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist U))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist S))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist R))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist A))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist H))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist C))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist P))
            (cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist N))) =
          some (CauchyNetCompletionUp.mk D W Q M U S R A H C P N)
      rw [CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode W,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode M,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode U,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode A,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyNetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyNetCompletionUp} :
    cauchyNetCompletionToEventFlow x = cauchyNetCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNetCompletionFromEventFlow (cauchyNetCompletionToEventFlow x) =
        cauchyNetCompletionFromEventFlow (cauchyNetCompletionToEventFlow y) :=
    congrArg cauchyNetCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyNetCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyNetCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyNetCompletionBHistCarrier : BHistCarrier CauchyNetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetCompletionToEventFlow
  fromEventFlow := cauchyNetCompletionFromEventFlow

instance cauchyNetCompletionChapterTasteGate : ChapterTasteGate CauchyNetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyNetCompletionFromEventFlow (cauchyNetCompletionToEventFlow x) = some x
    exact CauchyNetCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyNetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyNetCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetCompletionChapterTasteGate

theorem CauchyNetCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyNetCompletionDecodeBHist (cauchyNetCompletionEncodeBHist h) = h) ∧
      (forall x : CauchyNetCompletionUp,
        cauchyNetCompletionFromEventFlow (cauchyNetCompletionToEventFlow x) = some x) ∧
        Nonempty (BHistCarrier CauchyNetCompletionUp) ∧
          Nonempty (ChapterTasteGate CauchyNetCompletionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CauchyNetCompletionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CauchyNetCompletionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · exact ⟨cauchyNetCompletionBHistCarrier⟩
      · exact ⟨cauchyNetCompletionChapterTasteGate⟩

end BEDC.Derived.CauchyNetCompletionUp
