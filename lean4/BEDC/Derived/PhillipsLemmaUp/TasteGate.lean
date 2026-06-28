import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhillipsLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhillipsLemmaUp : Type where
  | mk (source target boundedLift dualRead approximation obstruction transport replay
      provenance name : BHist) : PhillipsLemmaUp
  deriving DecidableEq

def phillipsLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: phillipsLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: phillipsLemmaEncodeBHist h

def phillipsLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (phillipsLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (phillipsLemmaDecodeBHist tail)

private theorem PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def phillipsLemmaFields : PhillipsLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhillipsLemmaUp.mk source target boundedLift dualRead approximation obstruction
      transport replay provenance name =>
      [source, target, boundedLift, dualRead, approximation, obstruction, transport,
        replay, provenance, name]

def phillipsLemmaToEventFlow : PhillipsLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (phillipsLemmaFields x).map phillipsLemmaEncodeBHist

private def phillipsLemmaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => phillipsLemmaEventAtDefault index rest

def phillipsLemmaFromEventFlow : EventFlow → Option PhillipsLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (PhillipsLemmaUp.mk
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 0 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 1 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 2 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 3 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 4 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 5 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 6 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 7 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 8 ef))
          (phillipsLemmaDecodeBHist (phillipsLemmaEventAtDefault 9 ef)))

private theorem PhillipsLemmaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PhillipsLemmaUp,
      phillipsLemmaFromEventFlow (phillipsLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target boundedLift dualRead approximation obstruction transport replay
      provenance name =>
      change
        some
          (PhillipsLemmaUp.mk
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist source))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist target))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist boundedLift))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist dualRead))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist approximation))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist obstruction))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist transport))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist replay))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist provenance))
            (phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist name))) =
          some
            (PhillipsLemmaUp.mk source target boundedLift dualRead approximation
              obstruction transport replay provenance name)
      rw [PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode source,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode target,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode boundedLift,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode dualRead,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode approximation,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode obstruction,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode transport,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode replay,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode provenance,
        PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode name]

private theorem PhillipsLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PhillipsLemmaUp} :
    phillipsLemmaToEventFlow x = phillipsLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      phillipsLemmaFromEventFlow (phillipsLemmaToEventFlow x) =
        phillipsLemmaFromEventFlow (phillipsLemmaToEventFlow y) :=
    congrArg phillipsLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PhillipsLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PhillipsLemmaTasteGate_single_carrier_alignment_round_trip y)))

instance phillipsLemmaBHistCarrier : BHistCarrier PhillipsLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := phillipsLemmaToEventFlow
  fromEventFlow := phillipsLemmaFromEventFlow

instance phillipsLemmaChapterTasteGate : ChapterTasteGate PhillipsLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change phillipsLemmaFromEventFlow (phillipsLemmaToEventFlow x) = some x
    exact PhillipsLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PhillipsLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PhillipsLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, phillipsLemmaDecodeBHist (phillipsLemmaEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PhillipsLemmaUp) ∧
        Nonempty (ChapterTasteGate PhillipsLemmaUp) ∧
          phillipsLemmaEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PhillipsLemmaTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨phillipsLemmaBHistCarrier⟩,
        ⟨⟨phillipsLemmaChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.PhillipsLemmaUp
