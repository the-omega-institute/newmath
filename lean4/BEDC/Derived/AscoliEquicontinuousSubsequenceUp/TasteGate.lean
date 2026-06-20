import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AscoliEquicontinuousSubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AscoliEquicontinuousSubsequenceUp : Type where
  | mk (A E K W R L D H C P N : BHist) : AscoliEquicontinuousSubsequenceUp
  deriving DecidableEq

def ascoliEquicontinuousSubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ascoliEquicontinuousSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ascoliEquicontinuousSubsequenceEncodeBHist h

def ascoliEquicontinuousSubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ascoliEquicontinuousSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ascoliEquicontinuousSubsequenceDecodeBHist tail)

private theorem AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ascoliEquicontinuousSubsequenceFields :
    AscoliEquicontinuousSubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AscoliEquicontinuousSubsequenceUp.mk A E K W R L D H C P N =>
      [A, E, K, W, R, L, D, H, C, P, N]

def ascoliEquicontinuousSubsequenceToEventFlow :
    AscoliEquicontinuousSubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (ascoliEquicontinuousSubsequenceFields x).map
      ascoliEquicontinuousSubsequenceEncodeBHist

private def ascoliEquicontinuousSubsequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ascoliEquicontinuousSubsequenceEventAtDefault index rest

def ascoliEquicontinuousSubsequenceFromEventFlow :
    EventFlow → Option AscoliEquicontinuousSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AscoliEquicontinuousSubsequenceUp.mk
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 0 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 1 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 2 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 3 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 4 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 5 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 6 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 7 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 8 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 9 ef))
        (ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEventAtDefault 10 ef)))

private theorem AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_round_trip
    (x : AscoliEquicontinuousSubsequenceUp) :
    ascoliEquicontinuousSubsequenceFromEventFlow
        (ascoliEquicontinuousSubsequenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A E K W R L D H C P N =>
      change
        some
          (AscoliEquicontinuousSubsequenceUp.mk
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist A))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist E))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist K))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist W))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist R))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist L))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist D))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist H))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist C))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist P))
            (ascoliEquicontinuousSubsequenceDecodeBHist
              (ascoliEquicontinuousSubsequenceEncodeBHist N))) =
          some (AscoliEquicontinuousSubsequenceUp.mk A E K W R L D H C P N)
      rw [AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode A,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode E,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode K,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode W,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode R,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode L,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode D,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode H,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode C,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode P,
        AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode N]

private theorem AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_toEventFlow_injective
    {x y : AscoliEquicontinuousSubsequenceUp} :
    ascoliEquicontinuousSubsequenceToEventFlow x =
        ascoliEquicontinuousSubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          ascoliEquicontinuousSubsequenceFromEventFlow
            (ascoliEquicontinuousSubsequenceToEventFlow x) :=
        (AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_round_trip x).symm
      _ =
          ascoliEquicontinuousSubsequenceFromEventFlow
            (ascoliEquicontinuousSubsequenceToEventFlow y) :=
        congrArg ascoliEquicontinuousSubsequenceFromEventFlow hxy
      _ = some y := AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance ascoliEquicontinuousSubsequenceBHistCarrier :
    BHistCarrier AscoliEquicontinuousSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ascoliEquicontinuousSubsequenceToEventFlow
  fromEventFlow := ascoliEquicontinuousSubsequenceFromEventFlow

instance ascoliEquicontinuousSubsequenceChapterTasteGate :
    ChapterTasteGate AscoliEquicontinuousSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ascoliEquicontinuousSubsequenceFromEventFlow
          (ascoliEquicontinuousSubsequenceToEventFlow x) =
        some x
    exact AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_toEventFlow_injective heq)

theorem AscoliEquicontinuousSubsequenceUp_single_carrier_alignment :
    (∀ h : BHist,
      ascoliEquicontinuousSubsequenceDecodeBHist
          (ascoliEquicontinuousSubsequenceEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier AscoliEquicontinuousSubsequenceUp) ∧
        Nonempty (ChapterTasteGate AscoliEquicontinuousSubsequenceUp) ∧
          ascoliEquicontinuousSubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨AscoliEquicontinuousSubsequenceUp_single_carrier_alignment_decode_encode,
      ⟨ascoliEquicontinuousSubsequenceBHistCarrier⟩,
      ⟨ascoliEquicontinuousSubsequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.AscoliEquicontinuousSubsequenceUp
