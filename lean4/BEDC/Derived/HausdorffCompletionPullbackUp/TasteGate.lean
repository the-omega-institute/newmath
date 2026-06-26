import BEDC.Derived.HausdorffCompletionPullbackUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffCompletionPullbackUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def hausdorffCompletionPullbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionPullbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionPullbackEncodeBHist h

def hausdorffCompletionPullbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionPullbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionPullbackDecodeBHist tail)

private theorem HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hausdorffCompletionPullbackDecodeBHist
          (hausdorffCompletionPullbackEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffCompletionPullbackFields :
    HausdorffCompletionPullbackUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionPullbackUp.mk S W D P0 P1 H0 H1 U T C Q N =>
      [S, W, D, P0, P1, H0, H1, U, T, C, Q, N]

def hausdorffCompletionPullbackToEventFlow :
    HausdorffCompletionPullbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffCompletionPullbackFields x).map hausdorffCompletionPullbackEncodeBHist

private def hausdorffCompletionPullbackEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffCompletionPullbackEventAt index rest

def hausdorffCompletionPullbackFromEventFlow (ef : EventFlow) :
    Option HausdorffCompletionPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffCompletionPullbackUp.mk
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 0 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 1 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 2 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 3 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 4 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 5 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 6 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 7 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 8 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 9 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 10 ef))
      (hausdorffCompletionPullbackDecodeBHist (hausdorffCompletionPullbackEventAt 11 ef)))

private theorem HausdorffCompletionPullbackTasteGate_single_carrier_alignment_round_trip
    (x : HausdorffCompletionPullbackUp) :
    hausdorffCompletionPullbackFromEventFlow
        (hausdorffCompletionPullbackToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W D P0 P1 H0 H1 U T C Q N =>
      change
        some
          (HausdorffCompletionPullbackUp.mk
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist S))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist W))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist D))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist P0))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist P1))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist H0))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist H1))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist U))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist T))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist C))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist Q))
            (hausdorffCompletionPullbackDecodeBHist
              (hausdorffCompletionPullbackEncodeBHist N))) =
          some (HausdorffCompletionPullbackUp.mk S W D P0 P1 H0 H1 U T C Q N)
      rw [HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode S,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode W,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode D,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode P0,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode P1,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode H0,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode H1,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode U,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode T,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode C,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode Q,
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode N]

private theorem HausdorffCompletionPullbackTasteGate_single_carrier_alignment_injective
    {x y : HausdorffCompletionPullbackUp} :
    hausdorffCompletionPullbackToEventFlow x =
        hausdorffCompletionPullbackToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffCompletionPullbackFromEventFlow (hausdorffCompletionPullbackToEventFlow x) =
        hausdorffCompletionPullbackFromEventFlow
          (hausdorffCompletionPullbackToEventFlow y) :=
    congrArg hausdorffCompletionPullbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HausdorffCompletionPullbackTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HausdorffCompletionPullbackTasteGate_single_carrier_alignment_round_trip y)))

instance hausdorffCompletionPullbackBHistCarrier :
    BHistCarrier HausdorffCompletionPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionPullbackToEventFlow
  fromEventFlow := hausdorffCompletionPullbackFromEventFlow

instance hausdorffCompletionPullbackChapterTasteGate :
    ChapterTasteGate HausdorffCompletionPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffCompletionPullbackFromEventFlow
          (hausdorffCompletionPullbackToEventFlow x) =
        some x
    exact HausdorffCompletionPullbackTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffCompletionPullbackTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate HausdorffCompletionPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffCompletionPullbackChapterTasteGate

theorem HausdorffCompletionPullbackTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hausdorffCompletionPullbackDecodeBHist
          (hausdorffCompletionPullbackEncodeBHist h) =
        h) ∧
      (∀ x : HausdorffCompletionPullbackUp,
        hausdorffCompletionPullbackFromEventFlow
            (hausdorffCompletionPullbackToEventFlow x) =
          some x) ∧
        (∀ x y : HausdorffCompletionPullbackUp,
          hausdorffCompletionPullbackToEventFlow x =
              hausdorffCompletionPullbackToEventFlow y →
            x = y) ∧
          hausdorffCompletionPullbackEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HausdorffCompletionPullbackTasteGate_single_carrier_alignment_decode_encode,
      HausdorffCompletionPullbackTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HausdorffCompletionPullbackTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.HausdorffCompletionPullbackUp
