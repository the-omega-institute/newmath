import BEDC.Derived.RealDiagonalWindowCoverageUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealDiagonalWindowCoverageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealDiagonalWindowCoverageUp : Type where
  | packet (q w r d e h c p n : BHist) : RealDiagonalWindowCoverageUp
  deriving DecidableEq

def realDiagonalWindowCoverageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realDiagonalWindowCoverageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realDiagonalWindowCoverageEncodeBHist h

def realDiagonalWindowCoverageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realDiagonalWindowCoverageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realDiagonalWindowCoverageDecodeBHist tail)

private theorem RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realDiagonalWindowCoverageFields : RealDiagonalWindowCoverageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealDiagonalWindowCoverageUp.packet q w r d e h c p n => [q, w, r, d, e, h, c, p, n]

def realDiagonalWindowCoverageToEventFlow : RealDiagonalWindowCoverageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realDiagonalWindowCoverageFields x).map realDiagonalWindowCoverageEncodeBHist

private def realDiagonalWindowCoverageEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realDiagonalWindowCoverageEventAt index rest

def realDiagonalWindowCoverageFromEventFlow (ef : EventFlow) :
    Option RealDiagonalWindowCoverageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealDiagonalWindowCoverageUp.packet
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 0 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 1 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 2 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 3 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 4 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 5 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 6 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 7 ef))
      (realDiagonalWindowCoverageDecodeBHist (realDiagonalWindowCoverageEventAt 8 ef)))

private theorem RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_round_trip
    (x : RealDiagonalWindowCoverageUp) :
    realDiagonalWindowCoverageFromEventFlow
        (realDiagonalWindowCoverageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet q w r d e h c p n =>
      change
        some
          (RealDiagonalWindowCoverageUp.packet
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist q))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist w))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist r))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist d))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist e))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist h))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist c))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist p))
            (realDiagonalWindowCoverageDecodeBHist
              (realDiagonalWindowCoverageEncodeBHist n))) =
          some (RealDiagonalWindowCoverageUp.packet q w r d e h c p n)
      rw [RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode q,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode w,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode r,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode d,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode e,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode h,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode c,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode p,
        RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_decode_encode n]

private theorem RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_injective
    {x y : RealDiagonalWindowCoverageUp} :
    realDiagonalWindowCoverageToEventFlow x = realDiagonalWindowCoverageToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realDiagonalWindowCoverageFromEventFlow (realDiagonalWindowCoverageToEventFlow x) =
        realDiagonalWindowCoverageFromEventFlow (realDiagonalWindowCoverageToEventFlow y) :=
    congrArg realDiagonalWindowCoverageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealDiagonalWindowCoverageUp,
      realDiagonalWindowCoverageFields x = realDiagonalWindowCoverageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet q₁ w₁ r₁ d₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | packet q₂ w₂ r₂ d₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance realDiagonalWindowCoverageBHistCarrier : BHistCarrier RealDiagonalWindowCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realDiagonalWindowCoverageToEventFlow
  fromEventFlow := realDiagonalWindowCoverageFromEventFlow

instance realDiagonalWindowCoverageChapterTasteGate :
    ChapterTasteGate RealDiagonalWindowCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realDiagonalWindowCoverageFromEventFlow
          (realDiagonalWindowCoverageToEventFlow x) = some x
    exact RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_injective heq)

instance realDiagonalWindowCoverageFieldFaithful :
    FieldFaithful RealDiagonalWindowCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realDiagonalWindowCoverageFields
  field_faithful :=
    RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_fields_faithful

instance realDiagonalWindowCoverageNontrivial : Nontrivial RealDiagonalWindowCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealDiagonalWindowCoverageUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealDiagonalWindowCoverageUp.packet (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RealDiagonalWindowCoverageTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RealDiagonalWindowCoverageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realDiagonalWindowCoverageChapterTasteGate

theorem RealDiagonalWindowCoverageTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealDiagonalWindowCoverageUp) ∧
      (∀ x : RealDiagonalWindowCoverageUp,
        ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
        realDiagonalWindowCoverageFields
            (RealDiagonalWindowCoverageUp.packet BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨realDiagonalWindowCoverageChapterTasteGate⟩
  · constructor
    · intro x
      exact ChapterTasteGate.no_hidden_input x
    · rfl

end BEDC.Derived.RealDiagonalWindowCoverageUp
