import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchauderBasisUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchauderBasisUp : Type where
  | mk :
      (vecSpace norm basisStream coordinate partialSum errorControl reconstruction transport
        replay provenance localName : BHist) →
        SchauderBasisUp
  deriving DecidableEq

def schauderBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schauderBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schauderBasisEncodeBHist h

def schauderBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schauderBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schauderBasisDecodeBHist tail)

private theorem SchauderBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, schauderBasisDecodeBHist (schauderBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schauderBasisToEventFlow : SchauderBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SchauderBasisUp.mk vecSpace norm basisStream coordinate partialSum errorControl
      reconstruction transport replay provenance localName =>
      [schauderBasisEncodeBHist vecSpace, schauderBasisEncodeBHist norm,
        schauderBasisEncodeBHist basisStream, schauderBasisEncodeBHist coordinate,
        schauderBasisEncodeBHist partialSum, schauderBasisEncodeBHist errorControl,
        schauderBasisEncodeBHist reconstruction, schauderBasisEncodeBHist transport,
        schauderBasisEncodeBHist replay, schauderBasisEncodeBHist provenance,
        schauderBasisEncodeBHist localName]

def schauderBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _ => event
  | Nat.succ n, [] => schauderBasisEventAtDefault n []
  | Nat.succ n, _ :: tail => schauderBasisEventAtDefault n tail

def schauderBasisFromEventFlow : EventFlow → Option SchauderBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SchauderBasisUp.mk
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 0 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 1 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 2 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 3 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 4 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 5 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 6 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 7 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 8 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 9 ef))
          (schauderBasisDecodeBHist (schauderBasisEventAtDefault 10 ef)))

private theorem SchauderBasisTasteGate_single_carrier_alignment_round_trip
    (x : SchauderBasisUp) :
    schauderBasisFromEventFlow (schauderBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk vecSpace norm basisStream coordinate partialSum errorControl reconstruction transport
      replay provenance localName =>
      change
        some
          (SchauderBasisUp.mk
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist vecSpace))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist norm))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist basisStream))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist coordinate))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist partialSum))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist errorControl))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist reconstruction))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist transport))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist replay))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist provenance))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist localName))) =
          some
            (SchauderBasisUp.mk vecSpace norm basisStream coordinate partialSum
              errorControl reconstruction transport replay provenance localName)
      rw [SchauderBasisTasteGate_single_carrier_alignment_decode_encode vecSpace,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode norm,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode basisStream,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode coordinate,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode partialSum,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode errorControl,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode reconstruction,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode transport,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode replay,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode provenance,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode localName]

private theorem SchauderBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SchauderBasisUp} :
    schauderBasisToEventFlow x = schauderBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schauderBasisFromEventFlow (schauderBasisToEventFlow x) =
        schauderBasisFromEventFlow (schauderBasisToEventFlow y) :=
    congrArg schauderBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SchauderBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SchauderBasisTasteGate_single_carrier_alignment_round_trip y)))

def schauderBasisCarrier : BHistCarrier SchauderBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schauderBasisToEventFlow
  fromEventFlow := schauderBasisFromEventFlow

instance schauderBasisBHistCarrier : BHistCarrier SchauderBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schauderBasisCarrier

def schauderBasisGate : @ChapterTasteGate SchauderBasisUp schauderBasisCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schauderBasisFromEventFlow (schauderBasisToEventFlow x) = some x
    exact SchauderBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchauderBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance schauderBasisChapterTasteGate : ChapterTasteGate SchauderBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schauderBasisGate

theorem SchauderBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, schauderBasisDecodeBHist (schauderBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SchauderBasisUp) ∧
        Nonempty (ChapterTasteGate SchauderBasisUp) ∧
          schauderBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SchauderBasisTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨schauderBasisCarrier⟩, ⟨⟨schauderBasisGate⟩, rfl⟩⟩⟩

end BEDC.Derived.SchauderBasisUp.TasteGate
