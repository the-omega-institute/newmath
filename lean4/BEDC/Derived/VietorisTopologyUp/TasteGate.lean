import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VietorisTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VietorisTopologyUp : Type where
  | mk (H K L U M T C P N : BHist) : VietorisTopologyUp
  deriving DecidableEq

def vietorisTopologyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: vietorisTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: vietorisTopologyEncodeBHist h

def vietorisTopologyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (vietorisTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (vietorisTopologyDecodeBHist tail)

private theorem VietorisTopologyTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def vietorisTopologyToEventFlow : VietorisTopologyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | VietorisTopologyUp.mk H K L U M T C P N =>
      [vietorisTopologyEncodeBHist H,
        vietorisTopologyEncodeBHist K,
        vietorisTopologyEncodeBHist L,
        vietorisTopologyEncodeBHist U,
        vietorisTopologyEncodeBHist M,
        vietorisTopologyEncodeBHist T,
        vietorisTopologyEncodeBHist C,
        vietorisTopologyEncodeBHist P,
        vietorisTopologyEncodeBHist N]

private def vietorisTopologyEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => vietorisTopologyEventAt index rest

def vietorisTopologyDecodeFields (ef : EventFlow) : VietorisTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  VietorisTopologyUp.mk
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 0 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 1 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 2 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 3 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 4 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 5 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 6 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 7 ef))
    (vietorisTopologyDecodeBHist (vietorisTopologyEventAt 8 ef))

def vietorisTopologyFromEventFlow : EventFlow -> Option VietorisTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef => some (vietorisTopologyDecodeFields ef)

private theorem VietorisTopologyTasteGate_single_carrier_alignment_round_trip
    (x : VietorisTopologyUp) :
    vietorisTopologyFromEventFlow (vietorisTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H K L U M T C P N =>
      change
        some
            (VietorisTopologyUp.mk
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist H))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist K))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist L))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist U))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist M))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist T))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist C))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist P))
              (vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist N))) =
          some (VietorisTopologyUp.mk H K L U M T C P N)
      rw [VietorisTopologyTasteGate_single_carrier_alignment_decode_encode H,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode K,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode L,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode U,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode M,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode T,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode C,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode P,
        VietorisTopologyTasteGate_single_carrier_alignment_decode_encode N]

private theorem VietorisTopologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VietorisTopologyUp} :
    vietorisTopologyToEventFlow x = vietorisTopologyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      vietorisTopologyFromEventFlow (vietorisTopologyToEventFlow x) =
        vietorisTopologyFromEventFlow (vietorisTopologyToEventFlow y) :=
    congrArg vietorisTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (VietorisTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (VietorisTopologyTasteGate_single_carrier_alignment_round_trip y)))

instance vietorisTopologyBHistCarrier : BHistCarrier VietorisTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := vietorisTopologyToEventFlow
  fromEventFlow := vietorisTopologyFromEventFlow

instance vietorisTopologyChapterTasteGate : ChapterTasteGate VietorisTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change vietorisTopologyFromEventFlow (vietorisTopologyToEventFlow x) = some x
    exact VietorisTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (VietorisTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem VietorisTopologyTasteGate_single_carrier_alignment :
    (forall h : BHist,
      vietorisTopologyDecodeBHist (vietorisTopologyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VietorisTopologyUp) ∧
        Nonempty (ChapterTasteGate VietorisTopologyUp) ∧
          vietorisTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨VietorisTopologyTasteGate_single_carrier_alignment_decode_encode,
      ⟨vietorisTopologyBHistCarrier⟩,
      ⟨vietorisTopologyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.VietorisTopologyUp
