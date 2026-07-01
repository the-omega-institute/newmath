import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformCauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformCauchyModulusUp : Type where
  | mk : (K F M S Q E H C P N : BHist) → CompactUniformCauchyModulusUp
  deriving DecidableEq

def compactUniformCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformCauchyModulusEncodeBHist h

def compactUniformCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformCauchyModulusDecodeBHist tail)

private theorem CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformCauchyModulusDecodeBHist
        (compactUniformCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformCauchyModulusFields : CompactUniformCauchyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformCauchyModulusUp.mk K F M S Q E H C P N => [K, F, M, S, Q, E, H, C, P, N]

def compactUniformCauchyModulusToEventFlow : CompactUniformCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformCauchyModulusFields x).map compactUniformCauchyModulusEncodeBHist

private def compactUniformCauchyModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformCauchyModulusEventAt index rest

def compactUniformCauchyModulusFromEventFlow :
    EventFlow → Option CompactUniformCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactUniformCauchyModulusUp.mk
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 0 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 1 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 2 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 3 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 4 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 5 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 6 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 7 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 8 ef))
        (compactUniformCauchyModulusDecodeBHist (compactUniformCauchyModulusEventAt 9 ef)))

private theorem CompactUniformCauchyModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformCauchyModulusUp,
      compactUniformCauchyModulusFromEventFlow
        (compactUniformCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M S Q E H C P N =>
      change
        some
          (CompactUniformCauchyModulusUp.mk
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist K))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist F))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist M))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist S))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist Q))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist E))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist H))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist C))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist P))
            (compactUniformCauchyModulusDecodeBHist
              (compactUniformCauchyModulusEncodeBHist N))) =
          some (CompactUniformCauchyModulusUp.mk K F M S Q E H C P N)
      rw [CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode K,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode F,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode M,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode S,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode Q,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode E,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode H,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode C,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode P,
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformCauchyModulusUp} :
    compactUniformCauchyModulusToEventFlow x =
      compactUniformCauchyModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformCauchyModulusFromEventFlow (compactUniformCauchyModulusToEventFlow x) =
        compactUniformCauchyModulusFromEventFlow (compactUniformCauchyModulusToEventFlow y) :=
    congrArg compactUniformCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactUniformCauchyModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformCauchyModulusTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformCauchyModulusBHistCarrier :
    BHistCarrier CompactUniformCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformCauchyModulusToEventFlow
  fromEventFlow := compactUniformCauchyModulusFromEventFlow

instance compactUniformCauchyModulusChapterTasteGate :
    ChapterTasteGate CompactUniformCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformCauchyModulusFromEventFlow
        (compactUniformCauchyModulusToEventFlow x) = some x
    exact CompactUniformCauchyModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactUniformCauchyModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformCauchyModulusDecodeBHist
        (compactUniformCauchyModulusEncodeBHist h) = h) ∧
      (∀ x : CompactUniformCauchyModulusUp,
        compactUniformCauchyModulusFromEventFlow
          (compactUniformCauchyModulusToEventFlow x) = some x) ∧
        (∀ x y : CompactUniformCauchyModulusUp,
          compactUniformCauchyModulusToEventFlow x =
            compactUniformCauchyModulusToEventFlow y → x = y) ∧
          compactUniformCauchyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactUniformCauchyModulusTasteGate_single_carrier_alignment_decode,
      CompactUniformCauchyModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactUniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactUniformCauchyModulusUp
