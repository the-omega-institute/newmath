import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationTerminationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationTerminationUp : Type where
  | mk (s t tau u b h p n : BHist) : ContinuationTerminationUp
  deriving DecidableEq

def continuationTerminationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationTerminationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationTerminationEncodeBHist h

def continuationTerminationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationTerminationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationTerminationDecodeBHist tail)

private theorem ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      continuationTerminationDecodeBHist (continuationTerminationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuationTerminationFields : ContinuationTerminationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationTerminationUp.mk s t tau u b h p n => [s, t, tau, u, b, h, p, n]

def continuationTerminationToEventFlow : ContinuationTerminationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (continuationTerminationFields x).map continuationTerminationEncodeBHist

private def continuationTerminationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuationTerminationEventAt index rest

def continuationTerminationFromEventFlow
    (ef : EventFlow) : Option ContinuationTerminationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuationTerminationUp.mk
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 0 ef))
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 1 ef))
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 2 ef))
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 3 ef))
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 4 ef))
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 5 ef))
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 6 ef))
      (continuationTerminationDecodeBHist (continuationTerminationEventAt 7 ef)))

private theorem ContinuationTerminationTasteGate_single_carrier_alignment_round_trip
    (x : ContinuationTerminationUp) :
    continuationTerminationFromEventFlow (continuationTerminationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk s t tau u b h p n =>
      change
        some
          (ContinuationTerminationUp.mk
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist s))
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist t))
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist tau))
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist u))
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist b))
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist h))
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist p))
            (continuationTerminationDecodeBHist (continuationTerminationEncodeBHist n))) =
          some (ContinuationTerminationUp.mk s t tau u b h p n)
      rw [ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode s,
        ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode t,
        ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode tau,
        ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode u,
        ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode b,
        ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode h,
        ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode p,
        ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode n]

private theorem ContinuationTerminationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuationTerminationUp} :
    continuationTerminationToEventFlow x = continuationTerminationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationTerminationFromEventFlow (continuationTerminationToEventFlow x) =
        continuationTerminationFromEventFlow (continuationTerminationToEventFlow y) :=
    congrArg continuationTerminationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContinuationTerminationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContinuationTerminationTasteGate_single_carrier_alignment_round_trip y)))

instance continuationTerminationBHistCarrier : BHistCarrier ContinuationTerminationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationTerminationToEventFlow
  fromEventFlow := continuationTerminationFromEventFlow

instance continuationTerminationChapterTasteGate :
    ChapterTasteGate ContinuationTerminationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuationTerminationFromEventFlow (continuationTerminationToEventFlow x) = some x
    exact ContinuationTerminationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContinuationTerminationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ContinuationTerminationTasteGate_single_carrier_alignment :
    (∀ h : BHist, continuationTerminationDecodeBHist (continuationTerminationEncodeBHist h) = h) ∧
      (∀ x : ContinuationTerminationUp,
        continuationTerminationFromEventFlow (continuationTerminationToEventFlow x) = some x) ∧
        (∀ x y : ContinuationTerminationUp,
          continuationTerminationToEventFlow x = continuationTerminationToEventFlow y → x = y) ∧
          continuationTerminationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ContinuationTerminationTasteGate_single_carrier_alignment_decode_encode,
      ContinuationTerminationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ContinuationTerminationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContinuationTerminationUp
