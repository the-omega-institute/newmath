import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FirstCountableSequentialClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FirstCountableSequentialClosureUp : Type where
  | mk (B T Q L W R D E H C P N : BHist) : FirstCountableSequentialClosureUp
  deriving DecidableEq

def firstCountableSequentialClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: firstCountableSequentialClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: firstCountableSequentialClosureEncodeBHist h

def firstCountableSequentialClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (firstCountableSequentialClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (firstCountableSequentialClosureDecodeBHist tail)

private theorem FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def firstCountableSequentialClosureFields : FirstCountableSequentialClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FirstCountableSequentialClosureUp.mk B T Q L W R D E H C P N =>
      [B, T, Q, L, W, R, D, E, H, C, P, N]

def firstCountableSequentialClosureToEventFlow :
    FirstCountableSequentialClosureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (firstCountableSequentialClosureFields x).map
    firstCountableSequentialClosureEncodeBHist

private def firstCountableSequentialClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      firstCountableSequentialClosureEventAtDefault index rest

def firstCountableSequentialClosureFromEventFlow
    (ef : EventFlow) : Option FirstCountableSequentialClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FirstCountableSequentialClosureUp.mk
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 0 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 1 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 2 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 3 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 4 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 5 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 6 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 7 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 8 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 9 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 10 ef))
      (firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEventAtDefault 11 ef)))

private theorem FirstCountableSequentialClosureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FirstCountableSequentialClosureUp,
      firstCountableSequentialClosureFromEventFlow
        (firstCountableSequentialClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B T Q L W R D E H C P N =>
      change
        some
          (FirstCountableSequentialClosureUp.mk
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist B))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist T))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist Q))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist L))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist W))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist R))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist D))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist E))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist H))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist C))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist P))
            (firstCountableSequentialClosureDecodeBHist
              (firstCountableSequentialClosureEncodeBHist N))) =
          some (FirstCountableSequentialClosureUp.mk B T Q L W R D E H C P N)
      rw [FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode B,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode T,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode Q,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode L,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode W,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode R,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode D,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode E,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode H,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode C,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode P,
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode N]

private theorem FirstCountableSequentialClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FirstCountableSequentialClosureUp} :
    firstCountableSequentialClosureToEventFlow x =
      firstCountableSequentialClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      firstCountableSequentialClosureFromEventFlow
          (firstCountableSequentialClosureToEventFlow x) =
        firstCountableSequentialClosureFromEventFlow
          (firstCountableSequentialClosureToEventFlow y) :=
    congrArg firstCountableSequentialClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FirstCountableSequentialClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FirstCountableSequentialClosureTasteGate_single_carrier_alignment_round_trip y)))

instance firstCountableSequentialClosureBHistCarrier :
    BHistCarrier FirstCountableSequentialClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := firstCountableSequentialClosureToEventFlow
  fromEventFlow := firstCountableSequentialClosureFromEventFlow

instance firstCountableSequentialClosureChapterTasteGate :
    ChapterTasteGate FirstCountableSequentialClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      firstCountableSequentialClosureFromEventFlow
        (firstCountableSequentialClosureToEventFlow x) = some x
    exact FirstCountableSequentialClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FirstCountableSequentialClosureTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate FirstCountableSequentialClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  firstCountableSequentialClosureChapterTasteGate

theorem FirstCountableSequentialClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      firstCountableSequentialClosureDecodeBHist
        (firstCountableSequentialClosureEncodeBHist h) = h) ∧
      (∀ x : FirstCountableSequentialClosureUp,
        firstCountableSequentialClosureFromEventFlow
          (firstCountableSequentialClosureToEventFlow x) = some x) ∧
        (∀ x y : FirstCountableSequentialClosureUp,
          firstCountableSequentialClosureToEventFlow x =
            firstCountableSequentialClosureToEventFlow y → x = y) ∧
          firstCountableSequentialClosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FirstCountableSequentialClosureTasteGate_single_carrier_alignment_decode,
      FirstCountableSequentialClosureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FirstCountableSequentialClosureTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.FirstCountableSequentialClosureUp
