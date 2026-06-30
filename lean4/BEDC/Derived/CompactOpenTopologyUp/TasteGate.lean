import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOpenTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactOpenTopologyUp : Type where
  | mk (K C S H P N : BHist) : CompactOpenTopologyUp
  deriving DecidableEq

def compactOpenTopologyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOpenTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOpenTopologyEncodeBHist h

def compactOpenTopologyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOpenTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOpenTopologyDecodeBHist tail)

private theorem CompactOpenTopologyTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      compactOpenTopologyDecodeBHist (compactOpenTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactOpenTopologyFields : CompactOpenTopologyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOpenTopologyUp.mk K C S H P N => [K, C, S, H, P, N]

def compactOpenTopologyToEventFlow : CompactOpenTopologyUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactOpenTopologyFields x).map compactOpenTopologyEncodeBHist

private def compactOpenTopologyEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactOpenTopologyEventAtDefault index rest

def compactOpenTopologyFromEventFlow (ef : EventFlow) : Option CompactOpenTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactOpenTopologyUp.mk
      (compactOpenTopologyDecodeBHist (compactOpenTopologyEventAtDefault 0 ef))
      (compactOpenTopologyDecodeBHist (compactOpenTopologyEventAtDefault 1 ef))
      (compactOpenTopologyDecodeBHist (compactOpenTopologyEventAtDefault 2 ef))
      (compactOpenTopologyDecodeBHist (compactOpenTopologyEventAtDefault 3 ef))
      (compactOpenTopologyDecodeBHist (compactOpenTopologyEventAtDefault 4 ef))
      (compactOpenTopologyDecodeBHist (compactOpenTopologyEventAtDefault 5 ef)))

theorem CompactOpenTopologyTasteGate_single_carrier_alignment :
    forall x : CompactOpenTopologyUp,
      compactOpenTopologyFromEventFlow (compactOpenTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K C S H P N =>
      change
        some
          (CompactOpenTopologyUp.mk
            (compactOpenTopologyDecodeBHist (compactOpenTopologyEncodeBHist K))
            (compactOpenTopologyDecodeBHist (compactOpenTopologyEncodeBHist C))
            (compactOpenTopologyDecodeBHist (compactOpenTopologyEncodeBHist S))
            (compactOpenTopologyDecodeBHist (compactOpenTopologyEncodeBHist H))
            (compactOpenTopologyDecodeBHist (compactOpenTopologyEncodeBHist P))
            (compactOpenTopologyDecodeBHist (compactOpenTopologyEncodeBHist N))) =
          some (CompactOpenTopologyUp.mk K C S H P N)
      rw [CompactOpenTopologyTasteGate_single_carrier_alignment_decode K,
        CompactOpenTopologyTasteGate_single_carrier_alignment_decode C,
        CompactOpenTopologyTasteGate_single_carrier_alignment_decode S,
        CompactOpenTopologyTasteGate_single_carrier_alignment_decode H,
        CompactOpenTopologyTasteGate_single_carrier_alignment_decode P,
        CompactOpenTopologyTasteGate_single_carrier_alignment_decode N]

private theorem CompactOpenTopologyTasteGate_single_carrier_alignment_injective
    {x y : CompactOpenTopologyUp} :
    compactOpenTopologyToEventFlow x = compactOpenTopologyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactOpenTopologyFromEventFlow (compactOpenTopologyToEventFlow x) =
        compactOpenTopologyFromEventFlow (compactOpenTopologyToEventFlow y) :=
    congrArg compactOpenTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactOpenTopologyTasteGate_single_carrier_alignment x).symm
      (Eq.trans hread (CompactOpenTopologyTasteGate_single_carrier_alignment y)))

instance compactOpenTopologyBHistCarrier : BHistCarrier CompactOpenTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOpenTopologyToEventFlow
  fromEventFlow := compactOpenTopologyFromEventFlow

instance compactOpenTopologyChapterTasteGate :
    ChapterTasteGate CompactOpenTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactOpenTopologyFromEventFlow (compactOpenTopologyToEventFlow x) = some x
    exact CompactOpenTopologyTasteGate_single_carrier_alignment x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactOpenTopologyTasteGate_single_carrier_alignment_injective heq)

end BEDC.Derived.CompactOpenTopologyUp
