import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolarizationIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolarizationIdentityUp : Type where
  | mk (F V I N Q H C R L : BHist) : PolarizationIdentityUp
  deriving DecidableEq

def polarizationIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: polarizationIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: polarizationIdentityEncodeBHist h

def polarizationIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (polarizationIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (polarizationIdentityDecodeBHist tail)

private theorem PolarizationIdentityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def polarizationIdentityFields : PolarizationIdentityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PolarizationIdentityUp.mk F V I N Q H C R L => [F, V, I, N, Q, H, C, R, L]

def polarizationIdentityToEventFlow : PolarizationIdentityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (polarizationIdentityFields x).map polarizationIdentityEncodeBHist

private def polarizationIdentityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => polarizationIdentityEventAtDefault index rest

def polarizationIdentityFromEventFlow (ef : EventFlow) : Option PolarizationIdentityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PolarizationIdentityUp.mk
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 0 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 1 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 2 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 3 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 4 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 5 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 6 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 7 ef))
      (polarizationIdentityDecodeBHist (polarizationIdentityEventAtDefault 8 ef)))

private theorem PolarizationIdentityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PolarizationIdentityUp,
      polarizationIdentityFromEventFlow (polarizationIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F V I N Q H C R L =>
      change
        some
          (PolarizationIdentityUp.mk
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist F))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist V))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist I))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist N))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist Q))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist H))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist C))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist R))
            (polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist L))) =
          some (PolarizationIdentityUp.mk F V I N Q H C R L)
      rw [PolarizationIdentityTasteGate_single_carrier_alignment_decode F,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode V,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode I,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode N,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode Q,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode H,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode C,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode R,
        PolarizationIdentityTasteGate_single_carrier_alignment_decode L]

private theorem PolarizationIdentityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PolarizationIdentityUp} :
    polarizationIdentityToEventFlow x = polarizationIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      polarizationIdentityFromEventFlow (polarizationIdentityToEventFlow x) =
        polarizationIdentityFromEventFlow (polarizationIdentityToEventFlow y) :=
    congrArg polarizationIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PolarizationIdentityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PolarizationIdentityTasteGate_single_carrier_alignment_round_trip y)))

instance polarizationIdentityBHistCarrier : BHistCarrier PolarizationIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := polarizationIdentityToEventFlow
  fromEventFlow := polarizationIdentityFromEventFlow

instance polarizationIdentityChapterTasteGate : ChapterTasteGate PolarizationIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change polarizationIdentityFromEventFlow (polarizationIdentityToEventFlow x) = some x
    exact PolarizationIdentityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PolarizationIdentityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PolarizationIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist, polarizationIdentityDecodeBHist (polarizationIdentityEncodeBHist h) = h) ∧
      (∀ x : PolarizationIdentityUp,
        polarizationIdentityFromEventFlow (polarizationIdentityToEventFlow x) = some x) ∧
        (∀ x y : PolarizationIdentityUp,
          polarizationIdentityToEventFlow x = polarizationIdentityToEventFlow y → x = y) ∧
          polarizationIdentityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PolarizationIdentityTasteGate_single_carrier_alignment_decode,
      PolarizationIdentityTasteGate_single_carrier_alignment_round_trip,
      fun x y => PolarizationIdentityTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.PolarizationIdentityUp
