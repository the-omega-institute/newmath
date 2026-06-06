import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopMonotoneRealConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopMonotoneRealConvergenceUp : Type where
  | mk (S B O L W Q D E H C P N : BHist) : BishopMonotoneRealConvergenceUp
  deriving DecidableEq

def bishopMonotoneRealConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopMonotoneRealConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopMonotoneRealConvergenceEncodeBHist h

def bishopMonotoneRealConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopMonotoneRealConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopMonotoneRealConvergenceDecodeBHist tail)

private theorem BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def bishopMonotoneRealConvergenceFields :
    BishopMonotoneRealConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopMonotoneRealConvergenceUp.mk S B O L W Q D E H C P N =>
      [S, B, O, L, W, Q, D, E, H, C, P, N]

def bishopMonotoneRealConvergenceToEventFlow :
    BishopMonotoneRealConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopMonotoneRealConvergenceFields x).map
        bishopMonotoneRealConvergenceEncodeBHist

private def bishopMonotoneRealConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopMonotoneRealConvergenceEventAt index rest

def bishopMonotoneRealConvergenceFromEventFlow (ef : EventFlow) :
    Option BishopMonotoneRealConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopMonotoneRealConvergenceUp.mk
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 0 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 1 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 2 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 3 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 4 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 5 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 6 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 7 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 8 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 9 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 10 ef))
      (bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEventAt 11 ef)))

private theorem BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_round_trip
    (x : BishopMonotoneRealConvergenceUp) :
    bishopMonotoneRealConvergenceFromEventFlow
      (bishopMonotoneRealConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S B O L W Q D E H C P N =>
      change
        some
          (BishopMonotoneRealConvergenceUp.mk
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist S))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist B))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist O))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist L))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist W))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist Q))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist D))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist E))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist H))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist C))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist P))
            (bishopMonotoneRealConvergenceDecodeBHist
              (bishopMonotoneRealConvergenceEncodeBHist N))) =
          some (BishopMonotoneRealConvergenceUp.mk S B O L W Q D E H C P N)
      rw [BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode S,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode B,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode O,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode L,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode Q,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode D,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopMonotoneRealConvergenceUp} :
    bishopMonotoneRealConvergenceToEventFlow x =
      bishopMonotoneRealConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopMonotoneRealConvergenceFromEventFlow
          (bishopMonotoneRealConvergenceToEventFlow x) =
        bishopMonotoneRealConvergenceFromEventFlow
          (bishopMonotoneRealConvergenceToEventFlow y) :=
    congrArg bishopMonotoneRealConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance bishopMonotoneRealConvergenceBHistCarrier :
    BHistCarrier BishopMonotoneRealConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopMonotoneRealConvergenceToEventFlow
  fromEventFlow := bishopMonotoneRealConvergenceFromEventFlow

instance bishopMonotoneRealConvergenceChapterTasteGate :
    ChapterTasteGate BishopMonotoneRealConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopMonotoneRealConvergenceFromEventFlow
        (bishopMonotoneRealConvergenceToEventFlow x) = some x
    exact BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopMonotoneRealConvergenceDecodeBHist
        (bishopMonotoneRealConvergenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopMonotoneRealConvergenceUp) ∧
      Nonempty (ChapterTasteGate BishopMonotoneRealConvergenceUp) ∧
      bishopMonotoneRealConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact BishopMonotoneRealConvergenceTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact Nonempty.intro bishopMonotoneRealConvergenceBHistCarrier
  constructor
  · exact Nonempty.intro bishopMonotoneRealConvergenceChapterTasteGate
  · rfl

end BEDC.Derived.BishopMonotoneRealConvergenceUp
