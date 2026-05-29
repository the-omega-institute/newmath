import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveCantorTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveCantorTheoremUp : Type where
  | mk (E W D G T F R H C P N : BHist) : ConstructiveCantorTheoremUp
  deriving DecidableEq

def constructiveCantorTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveCantorTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveCantorTheoremEncodeBHist h

def constructiveCantorTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveCantorTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveCantorTheoremDecodeBHist tail)

private theorem ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveCantorTheoremDecodeBHist
          (constructiveCantorTheoremEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveCantorTheoremFields :
    ConstructiveCantorTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveCantorTheoremUp.mk E W D G T F R H C P N =>
      [E, W, D, G, T, F, R, H, C, P, N]

def constructiveCantorTheoremToEventFlow :
    ConstructiveCantorTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constructiveCantorTheoremFields x).map constructiveCantorTheoremEncodeBHist

private def constructiveCantorTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveCantorTheoremEventAt index rest

def constructiveCantorTheoremFromEventFlow
    (ef : EventFlow) : Option ConstructiveCantorTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveCantorTheoremUp.mk
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 0 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 1 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 2 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 3 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 4 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 5 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 6 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 7 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 8 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 9 ef))
      (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEventAt 10 ef)))

private theorem ConstructiveCantorTheoremTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveCantorTheoremUp) :
    constructiveCantorTheoremFromEventFlow
        (constructiveCantorTheoremToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E W D G T F R H C P N =>
      change
        some
          (ConstructiveCantorTheoremUp.mk
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist E))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist W))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist D))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist G))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist T))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist F))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist R))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist H))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist C))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist P))
            (constructiveCantorTheoremDecodeBHist (constructiveCantorTheoremEncodeBHist N))) =
          some (ConstructiveCantorTheoremUp.mk E W D G T F R H C P N)
      rw [ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode W,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode D,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode G,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode T,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode F,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveCantorTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveCantorTheoremUp} :
    constructiveCantorTheoremToEventFlow x =
        constructiveCantorTheoremToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveCantorTheoremFromEventFlow
          (constructiveCantorTheoremToEventFlow x) =
        constructiveCantorTheoremFromEventFlow
          (constructiveCantorTheoremToEventFlow y) :=
    congrArg constructiveCantorTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveCantorTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveCantorTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveCantorTheoremBHistCarrier :
    BHistCarrier ConstructiveCantorTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveCantorTheoremToEventFlow
  fromEventFlow := constructiveCantorTheoremFromEventFlow

instance constructiveCantorTheoremChapterTasteGate :
    ChapterTasteGate ConstructiveCantorTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveCantorTheoremFromEventFlow
          (constructiveCantorTheoremToEventFlow x) =
        some x
    exact ConstructiveCantorTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveCantorTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ConstructiveCantorTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveCantorTheoremDecodeBHist
      (constructiveCantorTheoremEncodeBHist h) = h) ∧
      (∀ x : ConstructiveCantorTheoremUp,
        constructiveCantorTheoremFromEventFlow
          (constructiveCantorTheoremToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveCantorTheoremUp,
          constructiveCantorTheoremToEventFlow x =
            constructiveCantorTheoremToEventFlow y → x = y) ∧
          constructiveCantorTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveCantorTheoremTasteGate_single_carrier_alignment_decode_encode,
      ConstructiveCantorTheoremTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ConstructiveCantorTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ConstructiveCantorTheoremUp
