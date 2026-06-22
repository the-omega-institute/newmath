import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverRadiusStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverRadiusStabilityUp : Type where
  | mk (K M probe R L U H C P N : BHist) : FiniteCoverRadiusStabilityUp
  deriving DecidableEq

def finiteCoverRadiusStabilityEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverRadiusStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverRadiusStabilityEncodeBHist h

def finiteCoverRadiusStabilityDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverRadiusStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverRadiusStabilityDecodeBHist tail)

private theorem FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCoverRadiusStabilityFields : FiniteCoverRadiusStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverRadiusStabilityUp.mk K M probe R L U H C P N =>
      [K, M, probe, R, L, U, H, C, P, N]

def finiteCoverRadiusStabilityToEventFlow : FiniteCoverRadiusStabilityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteCoverRadiusStabilityFields x).map finiteCoverRadiusStabilityEncodeBHist

private def finiteCoverRadiusStabilityEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCoverRadiusStabilityEventAtDefault index rest

def finiteCoverRadiusStabilityFromEventFlow
    (ef : EventFlow) : Option FiniteCoverRadiusStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteCoverRadiusStabilityUp.mk
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 0 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 1 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 2 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 3 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 4 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 5 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 6 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 7 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 8 ef))
      (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEventAtDefault 9 ef)))

private theorem FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteCoverRadiusStabilityUp,
      finiteCoverRadiusStabilityFromEventFlow (finiteCoverRadiusStabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M probe R L U H C P N =>
      change
        some
          (FiniteCoverRadiusStabilityUp.mk
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist K))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist M))
            (finiteCoverRadiusStabilityDecodeBHist
              (finiteCoverRadiusStabilityEncodeBHist probe))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist R))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist L))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist U))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist H))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist C))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist P))
            (finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist N))) =
          some (FiniteCoverRadiusStabilityUp.mk K M probe R L U H C P N)
      rw [FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode K,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode M,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode probe,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode R,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode L,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode U,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode H,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode C,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode P,
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode N]

private theorem FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteCoverRadiusStabilityUp} :
    finiteCoverRadiusStabilityToEventFlow x = finiteCoverRadiusStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCoverRadiusStabilityFromEventFlow (finiteCoverRadiusStabilityToEventFlow x) =
        finiteCoverRadiusStabilityFromEventFlow (finiteCoverRadiusStabilityToEventFlow y) :=
    congrArg finiteCoverRadiusStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_round_trip y)))

instance finiteCoverRadiusStabilityBHistCarrier :
    BHistCarrier FiniteCoverRadiusStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverRadiusStabilityToEventFlow
  fromEventFlow := finiteCoverRadiusStabilityFromEventFlow

instance finiteCoverRadiusStabilityChapterTasteGate :
    ChapterTasteGate FiniteCoverRadiusStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteCoverRadiusStabilityFromEventFlow (finiteCoverRadiusStabilityToEventFlow x) =
        some x
    exact FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteCoverRadiusStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteCoverRadiusStabilityChapterTasteGate

theorem FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteCoverRadiusStabilityDecodeBHist (finiteCoverRadiusStabilityEncodeBHist h) = h) ∧
      (∀ x : FiniteCoverRadiusStabilityUp,
        finiteCoverRadiusStabilityFromEventFlow (finiteCoverRadiusStabilityToEventFlow x) = some x) ∧
        (∀ x y : FiniteCoverRadiusStabilityUp,
          finiteCoverRadiusStabilityToEventFlow x = finiteCoverRadiusStabilityToEventFlow y →
            x = y) ∧
          finiteCoverRadiusStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_decode,
      FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_round_trip,
      fun x y heq =>
        FiniteCoverRadiusStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FiniteCoverRadiusStabilityUp
