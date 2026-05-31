import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailModulusLimitHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailModulusLimitHandoffUp : Type where
  | mk (Mu Tau S R D E H C P N : BHist) : TailModulusLimitHandoffUp
  deriving DecidableEq

def tailModulusLimitHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailModulusLimitHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailModulusLimitHandoffEncodeBHist h

def tailModulusLimitHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailModulusLimitHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailModulusLimitHandoffDecodeBHist tail)

private theorem TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tailModulusLimitHandoffFields :
    TailModulusLimitHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TailModulusLimitHandoffUp.mk Mu Tau S R D E H C P N =>
      [Mu, Tau, S, R, D, E, H, C, P, N]

def tailModulusLimitHandoffToEventFlow :
    TailModulusLimitHandoffUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (tailModulusLimitHandoffFields x).map
      tailModulusLimitHandoffEncodeBHist

private def tailModulusLimitHandoffEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      tailModulusLimitHandoffEventAtDefault index rest

def tailModulusLimitHandoffFromEventFlow
    (ef : EventFlow) : Option TailModulusLimitHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TailModulusLimitHandoffUp.mk
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 0 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 1 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 2 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 3 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 4 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 5 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 6 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 7 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 8 ef))
      (tailModulusLimitHandoffDecodeBHist
        (tailModulusLimitHandoffEventAtDefault 9 ef)))

private theorem TailModulusLimitHandoffTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TailModulusLimitHandoffUp,
      tailModulusLimitHandoffFromEventFlow
        (tailModulusLimitHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Mu Tau S R D E H C P N =>
      change
        some
            (TailModulusLimitHandoffUp.mk
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist Mu))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist Tau))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist S))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist R))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist D))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist E))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist H))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist C))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist P))
              (tailModulusLimitHandoffDecodeBHist
                (tailModulusLimitHandoffEncodeBHist N))) =
          some (TailModulusLimitHandoffUp.mk Mu Tau S R D E H C P N)
      rw [TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode Mu,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode Tau,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode S,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode R,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode D,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode E,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode H,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode C,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode P,
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode N]

private theorem TailModulusLimitHandoffTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TailModulusLimitHandoffUp} :
    tailModulusLimitHandoffToEventFlow x =
        tailModulusLimitHandoffToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tailModulusLimitHandoffFromEventFlow
          (tailModulusLimitHandoffToEventFlow x) =
        tailModulusLimitHandoffFromEventFlow
          (tailModulusLimitHandoffToEventFlow y) :=
    congrArg tailModulusLimitHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TailModulusLimitHandoffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TailModulusLimitHandoffTasteGate_single_carrier_alignment_round_trip y)))

instance tailModulusLimitHandoffBHistCarrier :
    BHistCarrier TailModulusLimitHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailModulusLimitHandoffToEventFlow
  fromEventFlow := tailModulusLimitHandoffFromEventFlow

instance tailModulusLimitHandoffChapterTasteGate :
    ChapterTasteGate TailModulusLimitHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      tailModulusLimitHandoffFromEventFlow
        (tailModulusLimitHandoffToEventFlow x) = some x
    exact TailModulusLimitHandoffTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (TailModulusLimitHandoffTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem TailModulusLimitHandoffTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        tailModulusLimitHandoffDecodeBHist
          (tailModulusLimitHandoffEncodeBHist h) = h) ∧
      (∀ x : TailModulusLimitHandoffUp,
        tailModulusLimitHandoffFromEventFlow
          (tailModulusLimitHandoffToEventFlow x) = some x) ∧
        (∀ x y : TailModulusLimitHandoffUp,
          tailModulusLimitHandoffToEventFlow x =
              tailModulusLimitHandoffToEventFlow y →
            x = y) ∧
          tailModulusLimitHandoffEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨TailModulusLimitHandoffTasteGate_single_carrier_alignment_decode_encode,
      TailModulusLimitHandoffTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        TailModulusLimitHandoffTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.TailModulusLimitHandoffUp
