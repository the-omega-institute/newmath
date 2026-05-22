import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopModulusRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopModulusRealUp : Type where
  | mk (M S D R E H C P N : BHist) : BishopModulusRealUp
  deriving DecidableEq

def bishopModulusRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopModulusRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopModulusRealEncodeBHist h

def bishopModulusRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopModulusRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopModulusRealDecodeBHist tail)

private theorem BishopModulusRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopModulusRealFields : BishopModulusRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopModulusRealUp.mk M S D R E H C P N => [M, S, D, R, E, H, C, P, N]

def bishopModulusRealToEventFlow : BishopModulusRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => bishopModulusRealFields x |>.map bishopModulusRealEncodeBHist

private def bishopModulusRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopModulusRealEventAt index rest

def bishopModulusRealFromEventFlow (ef : EventFlow) : Option BishopModulusRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopModulusRealUp.mk
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 0 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 1 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 2 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 3 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 4 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 5 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 6 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 7 ef))
      (bishopModulusRealDecodeBHist (bishopModulusRealEventAt 8 ef)))

private theorem BishopModulusRealTasteGate_single_carrier_alignment_round_trip
    (x : BishopModulusRealUp) :
    bishopModulusRealFromEventFlow (bishopModulusRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S D R E H C P N =>
      change
        some
          (BishopModulusRealUp.mk
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist M))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist S))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist D))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist R))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist E))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist H))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist C))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist P))
            (bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist N))) =
          some (BishopModulusRealUp.mk M S D R E H C P N)
      rw [BishopModulusRealTasteGate_single_carrier_alignment_decode_encode M,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode S,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode D,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode R,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode E,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode H,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode C,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode P,
        BishopModulusRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopModulusRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopModulusRealUp} :
    bishopModulusRealToEventFlow x = bishopModulusRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopModulusRealFromEventFlow (bishopModulusRealToEventFlow x) =
        bishopModulusRealFromEventFlow (bishopModulusRealToEventFlow y) :=
    congrArg bishopModulusRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopModulusRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopModulusRealTasteGate_single_carrier_alignment_round_trip y)))

instance bishopModulusRealBHistCarrier : BHistCarrier BishopModulusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopModulusRealToEventFlow
  fromEventFlow := bishopModulusRealFromEventFlow

instance bishopModulusRealChapterTasteGate : ChapterTasteGate BishopModulusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopModulusRealFromEventFlow (bishopModulusRealToEventFlow x) = some x
    exact BishopModulusRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopModulusRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopModulusRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopModulusRealDecodeBHist (bishopModulusRealEncodeBHist h) = h) ∧
      (∀ x : BishopModulusRealUp,
        bishopModulusRealFromEventFlow (bishopModulusRealToEventFlow x) = some x) ∧
        (∀ x y : BishopModulusRealUp,
          bishopModulusRealToEventFlow x = bishopModulusRealToEventFlow y → x = y) ∧
          bishopModulusRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopModulusRealTasteGate_single_carrier_alignment_decode_encode,
      BishopModulusRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopModulusRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopModulusRealUp
