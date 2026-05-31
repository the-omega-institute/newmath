import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithCompletionUp : Type where
  | mk (D C G Q S R A H K P N : BHist) : MooreSmithCompletionUp
  deriving DecidableEq

def mooreSmithCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithCompletionEncodeBHist h

def mooreSmithCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithCompletionDecodeBHist tail)

private theorem MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mooreSmithCompletionToEventFlow : MooreSmithCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithCompletionUp.mk D C G Q S R A H K P N =>
      [[BMark.b0],
        mooreSmithCompletionEncodeBHist D,
        [BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        mooreSmithCompletionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mooreSmithCompletionEncodeBHist N]

private def mooreSmithCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mooreSmithCompletionEventAtDefault index rest

def mooreSmithCompletionFromEventFlow (ef : EventFlow) : Option MooreSmithCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MooreSmithCompletionUp.mk
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 1 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 3 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 5 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 7 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 9 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 11 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 13 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 15 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 17 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 19 ef))
      (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEventAtDefault 21 ef)))

private theorem MooreSmithCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MooreSmithCompletionUp,
      mooreSmithCompletionFromEventFlow (mooreSmithCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D C G Q S R A H K P N =>
      change
        some
          (MooreSmithCompletionUp.mk
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist D))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist C))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist G))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist Q))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist S))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist R))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist A))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist H))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist K))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist P))
            (mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist N))) =
          some (MooreSmithCompletionUp.mk D C G Q S R A H K P N)
      rw [MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode D,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode C,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode G,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode S,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode R,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode A,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode H,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode K,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode P,
        MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem MooreSmithCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MooreSmithCompletionUp} :
    mooreSmithCompletionToEventFlow x = mooreSmithCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithCompletionFromEventFlow (mooreSmithCompletionToEventFlow x) =
        mooreSmithCompletionFromEventFlow (mooreSmithCompletionToEventFlow y) :=
    congrArg mooreSmithCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MooreSmithCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MooreSmithCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance mooreSmithCompletionBHistCarrier : BHistCarrier MooreSmithCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithCompletionToEventFlow
  fromEventFlow := mooreSmithCompletionFromEventFlow

instance mooreSmithCompletionChapterTasteGate : ChapterTasteGate MooreSmithCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mooreSmithCompletionFromEventFlow (mooreSmithCompletionToEventFlow x) = some x
    exact MooreSmithCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MooreSmithCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MooreSmithCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithCompletionChapterTasteGate

theorem MooreSmithCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, mooreSmithCompletionDecodeBHist (mooreSmithCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MooreSmithCompletionUp) ∧
        Nonempty (ChapterTasteGate MooreSmithCompletionUp) ∧
          mooreSmithCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MooreSmithCompletionTasteGate_single_carrier_alignment_decode_encode,
      ⟨mooreSmithCompletionBHistCarrier⟩,
      ⟨mooreSmithCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MooreSmithCompletionUp
