import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactoidUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactoidUp : Type where
  | mk
      (uniform located finiteNet precompact compactMetric completeUniform realUniform transport
        replay provenance name : BHist) :
      CompactoidUp
  deriving DecidableEq

def compactoidEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactoidEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactoidEncodeBHist h

def compactoidDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactoidDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactoidDecodeBHist tail)

private theorem CompactoidTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, compactoidDecodeBHist (compactoidEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactoidFields : CompactoidUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactoidUp.mk uniform located finiteNet precompact compactMetric completeUniform
      realUniform transport replay provenance name =>
      [uniform, located, finiteNet, precompact, compactMetric, completeUniform,
        realUniform, transport, replay, provenance, name]

def compactoidToEventFlow : CompactoidUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactoidFields x).map compactoidEncodeBHist

private def compactoidEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactoidEventAtDefault index rest

def compactoidFromEventFlow : EventFlow → Option CompactoidUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactoidUp.mk
        (compactoidDecodeBHist (compactoidEventAtDefault 0 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 1 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 2 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 3 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 4 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 5 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 6 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 7 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 8 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 9 ef))
        (compactoidDecodeBHist (compactoidEventAtDefault 10 ef)))

private theorem CompactoidTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactoidUp,
      compactoidFromEventFlow (compactoidToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk uniform located finiteNet precompact compactMetric completeUniform realUniform
      transport replay provenance name =>
      change
        some
          (CompactoidUp.mk
            (compactoidDecodeBHist (compactoidEncodeBHist uniform))
            (compactoidDecodeBHist (compactoidEncodeBHist located))
            (compactoidDecodeBHist (compactoidEncodeBHist finiteNet))
            (compactoidDecodeBHist (compactoidEncodeBHist precompact))
            (compactoidDecodeBHist (compactoidEncodeBHist compactMetric))
            (compactoidDecodeBHist (compactoidEncodeBHist completeUniform))
            (compactoidDecodeBHist (compactoidEncodeBHist realUniform))
            (compactoidDecodeBHist (compactoidEncodeBHist transport))
            (compactoidDecodeBHist (compactoidEncodeBHist replay))
            (compactoidDecodeBHist (compactoidEncodeBHist provenance))
            (compactoidDecodeBHist (compactoidEncodeBHist name))) =
          some
            (CompactoidUp.mk uniform located finiteNet precompact compactMetric
              completeUniform realUniform transport replay provenance name)
      rw [CompactoidTasteGate_single_carrier_alignment_decode_encode uniform,
        CompactoidTasteGate_single_carrier_alignment_decode_encode located,
        CompactoidTasteGate_single_carrier_alignment_decode_encode finiteNet,
        CompactoidTasteGate_single_carrier_alignment_decode_encode precompact,
        CompactoidTasteGate_single_carrier_alignment_decode_encode compactMetric,
        CompactoidTasteGate_single_carrier_alignment_decode_encode completeUniform,
        CompactoidTasteGate_single_carrier_alignment_decode_encode realUniform,
        CompactoidTasteGate_single_carrier_alignment_decode_encode transport,
        CompactoidTasteGate_single_carrier_alignment_decode_encode replay,
        CompactoidTasteGate_single_carrier_alignment_decode_encode provenance,
        CompactoidTasteGate_single_carrier_alignment_decode_encode name]

private theorem CompactoidTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactoidUp} :
    compactoidToEventFlow x = compactoidToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactoidFromEventFlow (compactoidToEventFlow x) =
        compactoidFromEventFlow (compactoidToEventFlow y) :=
    congrArg compactoidFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactoidTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactoidTasteGate_single_carrier_alignment_round_trip y)))

instance compactoidBHistCarrier : BHistCarrier CompactoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactoidToEventFlow
  fromEventFlow := compactoidFromEventFlow

instance compactoidChapterTasteGate : ChapterTasteGate CompactoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactoidFromEventFlow (compactoidToEventFlow x) = some x
    exact CompactoidTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactoidTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactoidUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactoidChapterTasteGate

theorem CompactoidTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactoidDecodeBHist (compactoidEncodeBHist h) = h) ∧
      (∀ x : CompactoidUp,
        compactoidFromEventFlow (compactoidToEventFlow x) = some x) ∧
        (∀ x y : CompactoidUp,
          compactoidToEventFlow x = compactoidToEventFlow y → x = y) ∧
          compactoidEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactoidTasteGate_single_carrier_alignment_decode_encode,
      CompactoidTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactoidTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactoidUp
