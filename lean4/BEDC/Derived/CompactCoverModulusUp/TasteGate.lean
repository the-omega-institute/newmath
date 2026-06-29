import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactCoverModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactCoverModulusUp : Type where
  | mk (K C L F R H P N : BHist) : CompactCoverModulusUp
  deriving DecidableEq

def compactCoverModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactCoverModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactCoverModulusEncodeBHist h

def compactCoverModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactCoverModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactCoverModulusDecodeBHist tail)

private theorem compactCoverModulusDecode_encode :
    ∀ h : BHist, compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactCoverModulusFields : CompactCoverModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactCoverModulusUp.mk K C L F R H P N => [K, C, L, F, R, H, P, N]

def compactCoverModulusToEventFlow : CompactCoverModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactCoverModulusFields x).map compactCoverModulusEncodeBHist

private def compactCoverModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactCoverModulusEventAtDefault index rest

def compactCoverModulusFromEventFlow (ef : EventFlow) : Option CompactCoverModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactCoverModulusUp.mk
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 0 ef))
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 1 ef))
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 2 ef))
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 3 ef))
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 4 ef))
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 5 ef))
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 6 ef))
      (compactCoverModulusDecodeBHist (compactCoverModulusEventAtDefault 7 ef)))

private theorem compactCoverModulus_round_trip :
    ∀ x : CompactCoverModulusUp,
      compactCoverModulusFromEventFlow (compactCoverModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K C L F R H P N =>
      change
        some
          (CompactCoverModulusUp.mk
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist K))
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist C))
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist L))
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist F))
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist R))
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist H))
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist P))
            (compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist N))) =
          some (CompactCoverModulusUp.mk K C L F R H P N)
      rw [compactCoverModulusDecode_encode K, compactCoverModulusDecode_encode C,
        compactCoverModulusDecode_encode L, compactCoverModulusDecode_encode F,
        compactCoverModulusDecode_encode R, compactCoverModulusDecode_encode H,
        compactCoverModulusDecode_encode P, compactCoverModulusDecode_encode N]

private theorem compactCoverModulusToEventFlow_injective {x y : CompactCoverModulusUp} :
    compactCoverModulusToEventFlow x = compactCoverModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactCoverModulusFromEventFlow (compactCoverModulusToEventFlow x) =
        compactCoverModulusFromEventFlow (compactCoverModulusToEventFlow y) :=
    congrArg compactCoverModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactCoverModulus_round_trip x).symm
      (Eq.trans hread (compactCoverModulus_round_trip y)))

instance compactCoverModulusBHistCarrier : BHistCarrier CompactCoverModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactCoverModulusToEventFlow
  fromEventFlow := compactCoverModulusFromEventFlow

instance compactCoverModulusChapterTasteGate : ChapterTasteGate CompactCoverModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactCoverModulusFromEventFlow (compactCoverModulusToEventFlow x) = some x
    exact compactCoverModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactCoverModulusToEventFlow_injective heq)

theorem CompactCoverModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompactCoverModulusUp) ∧
      Nonempty (ChapterTasteGate CompactCoverModulusUp) ∧
      (∀ h : BHist, compactCoverModulusDecodeBHist (compactCoverModulusEncodeBHist h) = h) ∧
      (∀ x : CompactCoverModulusUp,
        compactCoverModulusFromEventFlow (compactCoverModulusToEventFlow x) = some x) ∧
      compactCoverModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨compactCoverModulusBHistCarrier⟩,
      ⟨compactCoverModulusChapterTasteGate⟩,
      compactCoverModulusDecode_encode,
      compactCoverModulus_round_trip,
      rfl⟩

end BEDC.Derived.CompactCoverModulusUp.TasteGate
