import BEDC.Derived.CompletionDenseRangeUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionDenseRangeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def completionDenseRangeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionDenseRangeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionDenseRangeEncodeBHist h

def completionDenseRangeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionDenseRangeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionDenseRangeDecodeBHist tail)

private theorem CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def completionDenseRangeFields :
    BEDC.Derived.CompletionDenseRangeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ⟨S, D, E, U, W, R, Q, H, C, P, N⟩ =>
      [S, D, E, U, W, R, Q, H, C, P, N]

def completionDenseRangeToEventFlow :
    BEDC.Derived.CompletionDenseRangeUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completionDenseRangeFields x).map completionDenseRangeEncodeBHist

private def completionDenseRangeEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionDenseRangeEventAt index rest

def completionDenseRangeFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.CompletionDenseRangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some {
    S := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 0 ef)
    D := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 1 ef)
    E := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 2 ef)
    U := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 3 ef)
    W := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 4 ef)
    R := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 5 ef)
    Q := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 6 ef)
    H := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 7 ef)
    C := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 8 ef)
    P := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 9 ef)
    N := completionDenseRangeDecodeBHist (completionDenseRangeEventAt 10 ef)
  }

private theorem CompletionDenseRangeTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.CompletionDenseRangeUp) :
    completionDenseRangeFromEventFlow (completionDenseRangeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D E U W R Q H C P N =>
      change
        some
          (BEDC.Derived.CompletionDenseRangeUp.mk
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist S))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist D))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist E))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist U))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist W))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist R))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist Q))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist H))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist C))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist P))
            (completionDenseRangeDecodeBHist (completionDenseRangeEncodeBHist N))) =
          some (BEDC.Derived.CompletionDenseRangeUp.mk S D E U W R Q H C P N)
      rw [CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode S,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode D,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode E,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode U,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode W,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode R,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode Q,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode H,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode C,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode P,
        CompletionDenseRangeTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompletionDenseRangeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.CompletionDenseRangeUp} :
    completionDenseRangeToEventFlow x = completionDenseRangeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionDenseRangeFromEventFlow (completionDenseRangeToEventFlow x) =
        completionDenseRangeFromEventFlow (completionDenseRangeToEventFlow y) :=
    congrArg completionDenseRangeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionDenseRangeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionDenseRangeTasteGate_single_carrier_alignment_round_trip y)))

instance completionDenseRangeBHistCarrier :
    BHistCarrier BEDC.Derived.CompletionDenseRangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionDenseRangeToEventFlow
  fromEventFlow := completionDenseRangeFromEventFlow

instance completionDenseRangeChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CompletionDenseRangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionDenseRangeFromEventFlow (completionDenseRangeToEventFlow x) = some x
    exact CompletionDenseRangeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompletionDenseRangeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompletionDenseRangeTasteGate_single_carrier_alignment :
    ChapterTasteGate BEDC.Derived.CompletionDenseRangeUp ∧
      (forall X : BEDC.Derived.CompletionDenseRangeUp,
        hsame X.S X.S ∧ hsame X.D X.D ∧ hsame X.E X.E ∧ hsame X.N X.N) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate hsame
  constructor
  · exact completionDenseRangeChapterTasteGate
  · intro X
    exact ⟨hsame_refl X.S, hsame_refl X.D, hsame_refl X.E, hsame_refl X.N⟩

end BEDC.Derived.CompletionDenseRangeUp
