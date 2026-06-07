import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusOfSequentialContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusOfSequentialContinuityUp : Type where
  | mk (X Y F S T E WX WY RX RY A H C P N : BHist) :
      ModulusOfSequentialContinuityUp
  deriving DecidableEq

def modulusOfSequentialContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusOfSequentialContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusOfSequentialContinuityEncodeBHist h

def modulusOfSequentialContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusOfSequentialContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusOfSequentialContinuityDecodeBHist tail)

private theorem ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusOfSequentialContinuityFields :
    ModulusOfSequentialContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusOfSequentialContinuityUp.mk X Y F S T E WX WY RX RY A H C P N =>
      [X, Y, F, S, T, E, WX, WY, RX, RY, A, H, C, P, N]

def modulusOfSequentialContinuityToEventFlow :
    ModulusOfSequentialContinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (modulusOfSequentialContinuityFields x).map
    modulusOfSequentialContinuityEncodeBHist

private def modulusOfSequentialContinuityEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => modulusOfSequentialContinuityEventAt index rest

def modulusOfSequentialContinuityFromEventFlow :
    EventFlow → Option ModulusOfSequentialContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ModulusOfSequentialContinuityUp.mk
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 0 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 1 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 2 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 3 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 4 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 5 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 6 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 7 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 8 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 9 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 10 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 11 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 12 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 13 ef))
        (modulusOfSequentialContinuityDecodeBHist
          (modulusOfSequentialContinuityEventAt 14 ef)))

private theorem ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ModulusOfSequentialContinuityUp,
      modulusOfSequentialContinuityFromEventFlow
          (modulusOfSequentialContinuityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y F S T E WX WY RX RY A H C P N =>
      change
        some
            (ModulusOfSequentialContinuityUp.mk
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist X))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist Y))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist F))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist S))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist T))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist E))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist WX))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist WY))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist RX))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist RY))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist A))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist H))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist C))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist P))
              (modulusOfSequentialContinuityDecodeBHist
                (modulusOfSequentialContinuityEncodeBHist N))) =
          some (ModulusOfSequentialContinuityUp.mk X Y F S T E WX WY RX RY A H C P N)
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode X]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode Y]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode F]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode S]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode T]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode E]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode WX]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode WY]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode RX]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode RY]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode A]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode H]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode C]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode P]
      rw [ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_injective
    {x y : ModulusOfSequentialContinuityUp} :
    modulusOfSequentialContinuityToEventFlow x =
        modulusOfSequentialContinuityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          modulusOfSequentialContinuityFromEventFlow
            (modulusOfSequentialContinuityToEventFlow x) :=
        (ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          modulusOfSequentialContinuityFromEventFlow
            (modulusOfSequentialContinuityToEventFlow y) :=
        congrArg modulusOfSequentialContinuityFromEventFlow hxy
      _ = some y :=
        ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance modulusOfSequentialContinuityBHistCarrier :
    BHistCarrier ModulusOfSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusOfSequentialContinuityToEventFlow
  fromEventFlow := modulusOfSequentialContinuityFromEventFlow

instance modulusOfSequentialContinuityChapterTasteGate :
    ChapterTasteGate ModulusOfSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      modulusOfSequentialContinuityFromEventFlow
          (modulusOfSequentialContinuityToEventFlow x) =
        some x
    exact ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ModulusOfSequentialContinuityTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate ModulusOfSequentialContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modulusOfSequentialContinuityChapterTasteGate

theorem ModulusOfSequentialContinuityTasteGate_single_carrier_alignment :
    ChapterTasteGate ModulusOfSequentialContinuityUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact modulusOfSequentialContinuityChapterTasteGate

end BEDC.Derived.ModulusOfSequentialContinuityUp
