import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MercerTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MercerTheoremUp : Type where
  | mk (K O F R L E H C P N : BHist) : MercerTheoremUp
  deriving DecidableEq

def mercerTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mercerTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mercerTheoremEncodeBHist h

def mercerTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mercerTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mercerTheoremDecodeBHist tail)

theorem MercerTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, mercerTheoremDecodeBHist (mercerTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mercerTheoremFields : MercerTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MercerTheoremUp.mk K O F R L E H C P N => [K, O, F, R, L, E, H, C, P, N]

def mercerTheoremToEventFlow : MercerTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (mercerTheoremFields x).map mercerTheoremEncodeBHist

private def mercerTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mercerTheoremEventAt index rest

def mercerTheoremFromEventFlow (ef : EventFlow) : Option MercerTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MercerTheoremUp.mk
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 0 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 1 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 2 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 3 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 4 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 5 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 6 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 7 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 8 ef))
      (mercerTheoremDecodeBHist (mercerTheoremEventAt 9 ef)))

private theorem MercerTheoremTasteGate_single_carrier_alignment_round_trip
    (x : MercerTheoremUp) :
    mercerTheoremFromEventFlow (mercerTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K O F R L E H C P N =>
      change
        some
          (MercerTheoremUp.mk
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist K))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist O))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist F))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist R))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist L))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist E))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist H))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist C))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist P))
            (mercerTheoremDecodeBHist (mercerTheoremEncodeBHist N))) =
          some (MercerTheoremUp.mk K O F R L E H C P N)
      rw [MercerTheoremTasteGate_single_carrier_alignment_decode_encode K,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode O,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode F,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode R,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode L,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode E,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode H,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode C,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode P,
        MercerTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem MercerTheoremToEventFlow_injective {x y : MercerTheoremUp} :
    mercerTheoremToEventFlow x = mercerTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mercerTheoremFromEventFlow (mercerTheoremToEventFlow x) =
        mercerTheoremFromEventFlow (mercerTheoremToEventFlow y) :=
    congrArg mercerTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MercerTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MercerTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance mercerTheoremBHistCarrier : BHistCarrier MercerTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mercerTheoremToEventFlow
  fromEventFlow := mercerTheoremFromEventFlow

instance mercerTheoremChapterTasteGate : ChapterTasteGate MercerTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mercerTheoremFromEventFlow (mercerTheoremToEventFlow x) = some x
    exact MercerTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MercerTheoremToEventFlow_injective heq)

def MercerTheoremTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MercerTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mercerTheoremChapterTasteGate

end BEDC.Derived.MercerTheoremUp
