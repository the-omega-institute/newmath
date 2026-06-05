import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CayleyTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CayleyTheoremUp : Type where
  | mk (G L I F H T P N : BHist) : CayleyTheoremUp
  deriving DecidableEq

def cayleyTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cayleyTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cayleyTheoremEncodeBHist h

def cayleyTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cayleyTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cayleyTheoremDecodeBHist tail)

private theorem CayleyTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cayleyTheoremFields : CayleyTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CayleyTheoremUp.mk G L I F H T P N => [G, L, I, F, H, T, P, N]

def cayleyTheoremToEventFlow : CayleyTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cayleyTheoremFields x).map cayleyTheoremEncodeBHist

private def CayleyTheoremTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CayleyTheoremTasteGate_single_carrier_alignment_eventAt index rest

def cayleyTheoremFromEventFlow (ef : EventFlow) : Option CayleyTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CayleyTheoremUp.mk
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cayleyTheoremDecodeBHist
        (CayleyTheoremTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem CayleyTheoremTasteGate_single_carrier_alignment_round_trip
    (x : CayleyTheoremUp) :
    cayleyTheoremFromEventFlow (cayleyTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G L I F H T P N =>
      change
        some
          (CayleyTheoremUp.mk
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist G))
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist L))
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist I))
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist F))
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist H))
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist T))
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist P))
            (cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist N))) =
          some (CayleyTheoremUp.mk G L I F H T P N)
      rw [CayleyTheoremTasteGate_single_carrier_alignment_decode_encode G,
        CayleyTheoremTasteGate_single_carrier_alignment_decode_encode L,
        CayleyTheoremTasteGate_single_carrier_alignment_decode_encode I,
        CayleyTheoremTasteGate_single_carrier_alignment_decode_encode F,
        CayleyTheoremTasteGate_single_carrier_alignment_decode_encode H,
        CayleyTheoremTasteGate_single_carrier_alignment_decode_encode T,
        CayleyTheoremTasteGate_single_carrier_alignment_decode_encode P,
        CayleyTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem CayleyTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CayleyTheoremUp} :
    cayleyTheoremToEventFlow x = cayleyTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cayleyTheoremFromEventFlow (cayleyTheoremToEventFlow x) =
        cayleyTheoremFromEventFlow (cayleyTheoremToEventFlow y) :=
    congrArg cayleyTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CayleyTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CayleyTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance cayleyTheoremBHistCarrier : BHistCarrier CayleyTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cayleyTheoremToEventFlow
  fromEventFlow := cayleyTheoremFromEventFlow

instance cayleyTheoremChapterTasteGate :
    ChapterTasteGate CayleyTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cayleyTheoremFromEventFlow (cayleyTheoremToEventFlow x) = some x
    exact CayleyTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CayleyTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CayleyTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, cayleyTheoremDecodeBHist (cayleyTheoremEncodeBHist h) = h) ∧
      (∀ x : CayleyTheoremUp,
        cayleyTheoremFromEventFlow (cayleyTheoremToEventFlow x) = some x) ∧
      (∀ x y : CayleyTheoremUp,
        cayleyTheoremToEventFlow x = cayleyTheoremToEventFlow y -> x = y) ∧
      cayleyTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CayleyTheoremTasteGate_single_carrier_alignment_decode_encode,
      CayleyTheoremTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => CayleyTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CayleyTheoremUp
