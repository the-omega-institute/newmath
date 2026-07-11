import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelSummabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelSummabilityUp : Type where
  | mk (S T M D W R E H C P N : BHist) : AbelSummabilityUp
  deriving DecidableEq

def abelSummabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelSummabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelSummabilityEncodeBHist h

def abelSummabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelSummabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelSummabilityDecodeBHist tail)

private theorem AbelSummabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, abelSummabilityDecodeBHist (abelSummabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def abelSummabilityFields : AbelSummabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelSummabilityUp.mk S T M D W R E H C P N => [S, T, M, D, W, R, E, H, C, P, N]

def abelSummabilityToEventFlow : AbelSummabilityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (abelSummabilityFields x).map abelSummabilityEncodeBHist

private def abelSummabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelSummabilityEventAtDefault index rest

def abelSummabilityFromEventFlow (ef : EventFlow) : Option AbelSummabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelSummabilityUp.mk
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 0 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 1 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 2 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 3 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 4 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 5 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 6 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 7 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 8 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 9 ef))
      (abelSummabilityDecodeBHist (abelSummabilityEventAtDefault 10 ef)))

private theorem AbelSummabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AbelSummabilityUp,
      abelSummabilityFromEventFlow (abelSummabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T M D W R E H C P N =>
      change
        some
          (AbelSummabilityUp.mk
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist S))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist T))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist M))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist D))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist W))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist R))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist E))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist H))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist C))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist P))
            (abelSummabilityDecodeBHist (abelSummabilityEncodeBHist N))) =
          some (AbelSummabilityUp.mk S T M D W R E H C P N)
      rw [AbelSummabilityTasteGate_single_carrier_alignment_decode S,
        AbelSummabilityTasteGate_single_carrier_alignment_decode T,
        AbelSummabilityTasteGate_single_carrier_alignment_decode M,
        AbelSummabilityTasteGate_single_carrier_alignment_decode D,
        AbelSummabilityTasteGate_single_carrier_alignment_decode W,
        AbelSummabilityTasteGate_single_carrier_alignment_decode R,
        AbelSummabilityTasteGate_single_carrier_alignment_decode E,
        AbelSummabilityTasteGate_single_carrier_alignment_decode H,
        AbelSummabilityTasteGate_single_carrier_alignment_decode C,
        AbelSummabilityTasteGate_single_carrier_alignment_decode P,
        AbelSummabilityTasteGate_single_carrier_alignment_decode N]

private theorem AbelSummabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelSummabilityUp} :
    abelSummabilityToEventFlow x = abelSummabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelSummabilityFromEventFlow (abelSummabilityToEventFlow x) =
        abelSummabilityFromEventFlow (abelSummabilityToEventFlow y) :=
    congrArg abelSummabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AbelSummabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelSummabilityTasteGate_single_carrier_alignment_round_trip y)))

instance abelSummabilityBHistCarrier : BHistCarrier AbelSummabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelSummabilityToEventFlow
  fromEventFlow := abelSummabilityFromEventFlow

instance abelSummabilityChapterTasteGate : ChapterTasteGate AbelSummabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelSummabilityFromEventFlow (abelSummabilityToEventFlow x) = some x
    exact AbelSummabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelSummabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AbelSummabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist, abelSummabilityDecodeBHist (abelSummabilityEncodeBHist h) = h) ∧
      (∀ x : AbelSummabilityUp,
        abelSummabilityFromEventFlow (abelSummabilityToEventFlow x) = some x) ∧
        (∀ x y : AbelSummabilityUp,
          abelSummabilityToEventFlow x = abelSummabilityToEventFlow y → x = y) ∧
          abelSummabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨AbelSummabilityTasteGate_single_carrier_alignment_decode,
      AbelSummabilityTasteGate_single_carrier_alignment_round_trip,
      fun x y => AbelSummabilityTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.AbelSummabilityUp
