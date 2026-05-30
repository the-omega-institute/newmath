import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionFunctorUp : Type where
  | mk (D W Q E F U H C P N : BHist) : RealCompletionFunctorUp
  deriving DecidableEq

private def realCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionFunctorEncodeBHist h

private def realCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionFunctorDecodeBHist tail)

private theorem RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def realCompletionFunctorFields : RealCompletionFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionFunctorUp.mk D W Q E F U H C P N => [D, W, Q, E, F, U, H, C, P, N]

private def realCompletionFunctorToEventFlow : RealCompletionFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCompletionFunctorFields x).map realCompletionFunctorEncodeBHist

private def realCompletionFunctorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCompletionFunctorEventAt index rest

private def realCompletionFunctorFromEventFlow (ef : EventFlow) :
    Option RealCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCompletionFunctorUp.mk
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 0 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 1 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 2 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 3 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 4 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 5 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 6 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 7 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 8 ef))
      (realCompletionFunctorDecodeBHist (realCompletionFunctorEventAt 9 ef)))

private theorem RealCompletionFunctorTasteGate_single_carrier_alignment_round_trip
    (x : RealCompletionFunctorUp) :
    realCompletionFunctorFromEventFlow (realCompletionFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W Q E F U H C P N =>
      change
        some
          (RealCompletionFunctorUp.mk
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist D))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist W))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist Q))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist E))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist F))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist U))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist H))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist C))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist P))
            (realCompletionFunctorDecodeBHist (realCompletionFunctorEncodeBHist N))) =
          some (RealCompletionFunctorUp.mk D W Q E F U H C P N)
      rw [RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode D,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode W,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode Q,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode E,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode F,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode U,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode H,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode C,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode P,
        RealCompletionFunctorTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealCompletionFunctorUp} :
    realCompletionFunctorToEventFlow x = realCompletionFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionFunctorFromEventFlow (realCompletionFunctorToEventFlow x) =
        realCompletionFunctorFromEventFlow (realCompletionFunctorToEventFlow y) :=
    congrArg realCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance realCompletionFunctorBHistCarrier : BHistCarrier RealCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionFunctorToEventFlow
  fromEventFlow := realCompletionFunctorFromEventFlow

instance realCompletionFunctorChapterTasteGate :
    ChapterTasteGate RealCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletionFunctorFromEventFlow (realCompletionFunctorToEventFlow x) = some x
    exact RealCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealCompletionFunctorTasteGate_single_carrier_alignment :
    ChapterTasteGate RealCompletionFunctorUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact realCompletionFunctorChapterTasteGate

end BEDC.Derived.RealCompletionFunctorUp
