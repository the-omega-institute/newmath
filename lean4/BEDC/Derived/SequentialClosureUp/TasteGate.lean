import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialClosureUp : Type where
  | mk (T M S Q L U W R A H C P N : BHist) : SequentialClosureUp
  deriving DecidableEq

def sequentialClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialClosureEncodeBHist h

def sequentialClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialClosureDecodeBHist tail)

private theorem SequentialClosureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sequentialClosureDecodeBHist (sequentialClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sequentialClosureFields : SequentialClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialClosureUp.mk T M S Q L U W R A H C P N =>
      [T, M, S, Q, L, U, W, R, A, H, C, P, N]

def sequentialClosureToEventFlow : SequentialClosureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sequentialClosureFields x).map sequentialClosureEncodeBHist

private def sequentialClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialClosureEventAtDefault index rest

def sequentialClosureFromEventFlow (ef : EventFlow) : Option SequentialClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialClosureUp.mk
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 0 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 1 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 2 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 3 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 4 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 5 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 6 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 7 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 8 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 9 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 10 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 11 ef))
      (sequentialClosureDecodeBHist (sequentialClosureEventAtDefault 12 ef)))

private theorem sequentialClosure_round_trip :
    ∀ x : SequentialClosureUp,
      sequentialClosureFromEventFlow (sequentialClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M S Q L U W R A H C P N =>
      change
        some
          (SequentialClosureUp.mk
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist T))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist M))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist S))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist Q))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist L))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist U))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist W))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist R))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist A))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist H))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist C))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist P))
            (sequentialClosureDecodeBHist (sequentialClosureEncodeBHist N))) =
          some (SequentialClosureUp.mk T M S Q L U W R A H C P N)
      rw [SequentialClosureTasteGate_single_carrier_alignment_decode T,
        SequentialClosureTasteGate_single_carrier_alignment_decode M,
        SequentialClosureTasteGate_single_carrier_alignment_decode S,
        SequentialClosureTasteGate_single_carrier_alignment_decode Q,
        SequentialClosureTasteGate_single_carrier_alignment_decode L,
        SequentialClosureTasteGate_single_carrier_alignment_decode U,
        SequentialClosureTasteGate_single_carrier_alignment_decode W,
        SequentialClosureTasteGate_single_carrier_alignment_decode R,
        SequentialClosureTasteGate_single_carrier_alignment_decode A,
        SequentialClosureTasteGate_single_carrier_alignment_decode H,
        SequentialClosureTasteGate_single_carrier_alignment_decode C,
        SequentialClosureTasteGate_single_carrier_alignment_decode P,
        SequentialClosureTasteGate_single_carrier_alignment_decode N]

private theorem SequentialClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialClosureUp} :
    sequentialClosureToEventFlow x = sequentialClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialClosureFromEventFlow (sequentialClosureToEventFlow x) =
        sequentialClosureFromEventFlow (sequentialClosureToEventFlow y) :=
    congrArg sequentialClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentialClosure_round_trip x).symm
      (Eq.trans hread (sequentialClosure_round_trip y)))

instance sequentialClosureBHistCarrier : BHistCarrier SequentialClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialClosureToEventFlow
  fromEventFlow := sequentialClosureFromEventFlow

instance sequentialClosureChapterTasteGate : ChapterTasteGate SequentialClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialClosureFromEventFlow (sequentialClosureToEventFlow x) = some x
    exact sequentialClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SequentialClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SequentialClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentialClosureChapterTasteGate

theorem SequentialClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist, sequentialClosureDecodeBHist (sequentialClosureEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SequentialClosureUp) ∧
        Nonempty (ChapterTasteGate SequentialClosureUp) ∧
          sequentialClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SequentialClosureTasteGate_single_carrier_alignment_decode,
      ⟨sequentialClosureBHistCarrier⟩,
      ⟨sequentialClosureChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SequentialClosureUp
