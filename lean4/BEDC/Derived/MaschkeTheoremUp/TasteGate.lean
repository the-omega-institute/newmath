import BEDC.Derived.MaschkeTheoremUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MaschkeTheoremUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def maschkeTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: maschkeTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: maschkeTheoremEncodeBHist h

def maschkeTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (maschkeTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (maschkeTheoremDecodeBHist tail)

private theorem MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def maschkeTheoremToEventFlow : MaschkeTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MaschkeTheoremUp.mk G V R X A Q H C P N =>
      [maschkeTheoremEncodeBHist G,
        maschkeTheoremEncodeBHist V,
        maschkeTheoremEncodeBHist R,
        maschkeTheoremEncodeBHist X,
        maschkeTheoremEncodeBHist A,
        maschkeTheoremEncodeBHist Q,
        maschkeTheoremEncodeBHist H,
        maschkeTheoremEncodeBHist C,
        maschkeTheoremEncodeBHist P,
        maschkeTheoremEncodeBHist N]

private def maschkeTheoremEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => maschkeTheoremEventAtDefault index rest

def maschkeTheoremFromEventFlow (ef : EventFlow) : Option MaschkeTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MaschkeTheoremUp.mk
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 0 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 1 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 2 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 3 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 4 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 5 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 6 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 7 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 8 ef))
      (maschkeTheoremDecodeBHist (maschkeTheoremEventAtDefault 9 ef)))

private theorem MaschkeTheoremTasteGate_single_carrier_alignment_round_trip
    (x : MaschkeTheoremUp) :
    maschkeTheoremFromEventFlow (maschkeTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G V R X A Q H C P N =>
      change
        some
          (MaschkeTheoremUp.mk
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist G))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist V))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist R))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist X))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist A))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist Q))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist H))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist C))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist P))
            (maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist N))) =
          some (MaschkeTheoremUp.mk G V R X A Q H C P N)
      rw [MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode G,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode V,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode R,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode X,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode A,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode Q,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode H,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode C,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode P,
        MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem MaschkeTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MaschkeTheoremUp} :
    maschkeTheoremToEventFlow x = maschkeTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      maschkeTheoremFromEventFlow (maschkeTheoremToEventFlow x) =
        maschkeTheoremFromEventFlow (maschkeTheoremToEventFlow y) :=
    congrArg maschkeTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MaschkeTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MaschkeTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance maschkeTheoremBHistCarrier : BHistCarrier MaschkeTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := maschkeTheoremToEventFlow
  fromEventFlow := maschkeTheoremFromEventFlow

instance maschkeTheoremChapterTasteGate : ChapterTasteGate MaschkeTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change maschkeTheoremFromEventFlow (maschkeTheoremToEventFlow x) = some x
    exact MaschkeTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MaschkeTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MaschkeTheoremTasteGate_single_carrier_alignment :
    (forall h : BHist, maschkeTheoremDecodeBHist (maschkeTheoremEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MaschkeTheoremUp) ∧
        Nonempty (ChapterTasteGate MaschkeTheoremUp) ∧
          maschkeTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MaschkeTheoremTasteGate_single_carrier_alignment_decode_encode,
      ⟨maschkeTheoremBHistCarrier⟩,
      ⟨maschkeTheoremChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MaschkeTheoremUp
