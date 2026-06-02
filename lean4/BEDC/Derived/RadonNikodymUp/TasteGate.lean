import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RadonNikodymUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RadonNikodymUp : Type where
  | mk (Mmu Mnu A D I Q S H C P N : BHist) : RadonNikodymUp
  deriving DecidableEq

def radonNikodymEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: radonNikodymEncodeBHist h
  | BHist.e1 h => BMark.b1 :: radonNikodymEncodeBHist h

def radonNikodymDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (radonNikodymDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (radonNikodymDecodeBHist tail)

private theorem RadonNikodymTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, radonNikodymDecodeBHist (radonNikodymEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def radonNikodymToEventFlow : RadonNikodymUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RadonNikodymUp.mk Mmu Mnu A D I Q S H C P N =>
      [radonNikodymEncodeBHist Mmu,
        radonNikodymEncodeBHist Mnu,
        radonNikodymEncodeBHist A,
        radonNikodymEncodeBHist D,
        radonNikodymEncodeBHist I,
        radonNikodymEncodeBHist Q,
        radonNikodymEncodeBHist S,
        radonNikodymEncodeBHist H,
        radonNikodymEncodeBHist C,
        radonNikodymEncodeBHist P,
        radonNikodymEncodeBHist N]

private def radonNikodymEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => radonNikodymEventAtDefault index rest

def radonNikodymFromEventFlow (ef : EventFlow) : Option RadonNikodymUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RadonNikodymUp.mk
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 0 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 1 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 2 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 3 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 4 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 5 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 6 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 7 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 8 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 9 ef))
      (radonNikodymDecodeBHist (radonNikodymEventAtDefault 10 ef)))

private theorem RadonNikodymTasteGate_single_carrier_alignment_round_trip
    (x : RadonNikodymUp) :
    radonNikodymFromEventFlow (radonNikodymToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Mmu Mnu A D I Q S H C P N =>
      change
        some
          (RadonNikodymUp.mk
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist Mmu))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist Mnu))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist A))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist D))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist I))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist Q))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist S))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist H))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist C))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist P))
            (radonNikodymDecodeBHist (radonNikodymEncodeBHist N))) =
          some (RadonNikodymUp.mk Mmu Mnu A D I Q S H C P N)
      rw [RadonNikodymTasteGate_single_carrier_alignment_decode_encode Mmu,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode Mnu,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode A,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode D,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode I,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode Q,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode S,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode H,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode C,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode P,
        RadonNikodymTasteGate_single_carrier_alignment_decode_encode N]

private theorem RadonNikodymTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RadonNikodymUp} :
    radonNikodymToEventFlow x = radonNikodymToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      radonNikodymFromEventFlow (radonNikodymToEventFlow x) =
        radonNikodymFromEventFlow (radonNikodymToEventFlow y) :=
    congrArg radonNikodymFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RadonNikodymTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RadonNikodymTasteGate_single_carrier_alignment_round_trip y)))

instance radonNikodymBHistCarrier : BHistCarrier RadonNikodymUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := radonNikodymToEventFlow
  fromEventFlow := radonNikodymFromEventFlow

instance radonNikodymChapterTasteGate : ChapterTasteGate RadonNikodymUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change radonNikodymFromEventFlow (radonNikodymToEventFlow x) = some x
    exact RadonNikodymTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RadonNikodymTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RadonNikodymTasteGate_single_carrier_alignment :
    (forall h : BHist, radonNikodymDecodeBHist (radonNikodymEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RadonNikodymUp) ∧
        Nonempty (ChapterTasteGate RadonNikodymUp) ∧
          radonNikodymEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RadonNikodymTasteGate_single_carrier_alignment_decode_encode,
      ⟨radonNikodymBHistCarrier⟩,
      ⟨radonNikodymChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RadonNikodymUp
