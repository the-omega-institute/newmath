import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OlivierTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OlivierTheoremUp : Type where
  | mk (A T M R E H C P N : BHist) : OlivierTheoremUp
  deriving DecidableEq

def olivierTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: olivierTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: olivierTheoremEncodeBHist h

def olivierTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (olivierTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (olivierTheoremDecodeBHist tail)

private theorem OlivierTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, olivierTheoremDecodeBHist (olivierTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def olivierTheoremFields : OlivierTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OlivierTheoremUp.mk A T M R E H C P N => [A, T, M, R, E, H, C, P, N]

def olivierTheoremToEventFlow : OlivierTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (olivierTheoremFields x).map olivierTheoremEncodeBHist

private def olivierTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => olivierTheoremEventAt index rest

def olivierTheoremFromEventFlow (ef : EventFlow) : Option OlivierTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OlivierTheoremUp.mk
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 0 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 1 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 2 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 3 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 4 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 5 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 6 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 7 ef))
      (olivierTheoremDecodeBHist (olivierTheoremEventAt 8 ef)))

private theorem OlivierTheoremTasteGate_single_carrier_alignment_round_trip
    (x : OlivierTheoremUp) :
    olivierTheoremFromEventFlow (olivierTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A T M R E H C P N =>
      change
        some
          (OlivierTheoremUp.mk
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist A))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist T))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist M))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist R))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist E))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist H))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist C))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist P))
            (olivierTheoremDecodeBHist (olivierTheoremEncodeBHist N))) =
          some (OlivierTheoremUp.mk A T M R E H C P N)
      rw [OlivierTheoremTasteGate_single_carrier_alignment_decode_encode A,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode T,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode M,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode R,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode E,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode H,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode C,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode P,
        OlivierTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem OlivierTheoremTasteGate_single_carrier_alignment_injective
    {x y : OlivierTheoremUp} :
    olivierTheoremToEventFlow x = olivierTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      olivierTheoremFromEventFlow (olivierTheoremToEventFlow x) =
        olivierTheoremFromEventFlow (olivierTheoremToEventFlow y) :=
    congrArg olivierTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OlivierTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OlivierTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance olivierTheoremBHistCarrier : BHistCarrier OlivierTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := olivierTheoremToEventFlow
  fromEventFlow := olivierTheoremFromEventFlow

instance olivierTheoremChapterTasteGate :
    ChapterTasteGate OlivierTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change olivierTheoremFromEventFlow (olivierTheoremToEventFlow x) = some x
    exact OlivierTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OlivierTheoremTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate OlivierTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  olivierTheoremChapterTasteGate

theorem OlivierTheoremTasteGate_single_carrier_alignment :
    (forall h : BHist, olivierTheoremDecodeBHist (olivierTheoremEncodeBHist h) = h) ∧
      (forall x : OlivierTheoremUp,
        olivierTheoremFromEventFlow (olivierTheoremToEventFlow x) = some x) ∧
        (forall x y : OlivierTheoremUp,
          olivierTheoremToEventFlow x = olivierTheoremToEventFlow y -> x = y) ∧
          olivierTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact OlivierTheoremTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact OlivierTheoremTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact OlivierTheoremTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.OlivierTheoremUp
