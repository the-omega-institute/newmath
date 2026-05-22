import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastRegularCauchyEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastRegularCauchyEquivalenceUp : Type where
  | mk (F S D Q E H C P N : BHist) : FastRegularCauchyEquivalenceUp
  deriving DecidableEq

def fastRegularCauchyEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastRegularCauchyEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastRegularCauchyEquivalenceEncodeBHist h

def fastRegularCauchyEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastRegularCauchyEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastRegularCauchyEquivalenceDecodeBHist tail)

private theorem FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastRegularCauchyEquivalenceFields : FastRegularCauchyEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastRegularCauchyEquivalenceUp.mk F S D Q E H C P N => [F, S, D, Q, E, H, C, P, N]

def fastRegularCauchyEquivalenceToEventFlow : FastRegularCauchyEquivalenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fastRegularCauchyEquivalenceFields x).map fastRegularCauchyEquivalenceEncodeBHist

private def fastRegularCauchyEquivalenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fastRegularCauchyEquivalenceEventAtDefault index rest

def fastRegularCauchyEquivalenceFromEventFlow
    (ef : EventFlow) : Option FastRegularCauchyEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FastRegularCauchyEquivalenceUp.mk
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 0 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 1 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 2 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 3 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 4 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 5 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 6 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 7 ef))
      (fastRegularCauchyEquivalenceDecodeBHist
        (fastRegularCauchyEquivalenceEventAtDefault 8 ef)))

private theorem FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FastRegularCauchyEquivalenceUp,
      fastRegularCauchyEquivalenceFromEventFlow (fastRegularCauchyEquivalenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S D Q E H C P N =>
      change
        some
          (FastRegularCauchyEquivalenceUp.mk
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist F))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist S))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist D))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist Q))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist E))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist H))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist C))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist P))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist N))) =
          some (FastRegularCauchyEquivalenceUp.mk F S D Q E H C P N)
      rw [FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode F,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode S,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode D,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode Q,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode E,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode H,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode C,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode P,
        FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode N]

private theorem FastRegularCauchyEquivalenceToEventFlow_injective
    {x y : FastRegularCauchyEquivalenceUp} :
    fastRegularCauchyEquivalenceToEventFlow x =
      fastRegularCauchyEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastRegularCauchyEquivalenceFromEventFlow
          (fastRegularCauchyEquivalenceToEventFlow x) =
        fastRegularCauchyEquivalenceFromEventFlow
          (fastRegularCauchyEquivalenceToEventFlow y) :=
    congrArg fastRegularCauchyEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

instance fastRegularCauchyEquivalenceBHistCarrier :
    BHistCarrier FastRegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastRegularCauchyEquivalenceToEventFlow
  fromEventFlow := fastRegularCauchyEquivalenceFromEventFlow

instance fastRegularCauchyEquivalenceChapterTasteGate :
    ChapterTasteGate FastRegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastRegularCauchyEquivalenceFromEventFlow
      (fastRegularCauchyEquivalenceToEventFlow x) = some x
    exact FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FastRegularCauchyEquivalenceToEventFlow_injective heq)

theorem FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        fastRegularCauchyEquivalenceDecodeBHist
          (fastRegularCauchyEquivalenceEncodeBHist h) = h) ∧
      (∀ x : FastRegularCauchyEquivalenceUp,
        fastRegularCauchyEquivalenceFromEventFlow
          (fastRegularCauchyEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : FastRegularCauchyEquivalenceUp,
          fastRegularCauchyEquivalenceToEventFlow x =
            fastRegularCauchyEquivalenceToEventFlow y → x = y) ∧
          fastRegularCauchyEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_decode,
      FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FastRegularCauchyEquivalenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FastRegularCauchyEquivalenceUp
