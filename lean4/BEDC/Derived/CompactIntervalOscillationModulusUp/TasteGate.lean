import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalOscillationModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalOscillationModulusUp : Type where
  | mk (L W R Q O M E H C P N : BHist) : CompactIntervalOscillationModulusUp
  deriving DecidableEq

def compactIntervalOscillationModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalOscillationModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalOscillationModulusEncodeBHist h

def compactIntervalOscillationModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalOscillationModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalOscillationModulusDecodeBHist tail)

private theorem CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactIntervalOscillationModulusFields :
    CompactIntervalOscillationModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalOscillationModulusUp.mk L W R Q O M E H C P N =>
      [L, W, R, Q, O, M, E, H, C, P, N]

def compactIntervalOscillationModulusToEventFlow :
    CompactIntervalOscillationModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactIntervalOscillationModulusFields x).map
        compactIntervalOscillationModulusEncodeBHist

private def compactIntervalOscillationModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactIntervalOscillationModulusEventAtDefault index rest

def compactIntervalOscillationModulusFromEventFlow
    (ef : EventFlow) : Option CompactIntervalOscillationModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactIntervalOscillationModulusUp.mk
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 0 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 1 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 2 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 3 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 4 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 5 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 6 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 7 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 8 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 9 ef))
      (compactIntervalOscillationModulusDecodeBHist
        (compactIntervalOscillationModulusEventAtDefault 10 ef)))

private theorem CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactIntervalOscillationModulusUp,
      compactIntervalOscillationModulusFromEventFlow
        (compactIntervalOscillationModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L W R Q O M E H C P N =>
      change
        some
          (CompactIntervalOscillationModulusUp.mk
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist L))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist W))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist R))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist Q))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist O))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist M))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist E))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist H))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist C))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist P))
            (compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist N))) =
          some (CompactIntervalOscillationModulusUp.mk L W R Q O M E H C P N)
      rw [CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode L,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode W,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode R,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode Q,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode O,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode M,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode E,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode H,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode C,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode P,
        CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode N]

private theorem CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_injective
    {x y : CompactIntervalOscillationModulusUp} :
    compactIntervalOscillationModulusToEventFlow x =
      compactIntervalOscillationModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalOscillationModulusFromEventFlow
          (compactIntervalOscillationModulusToEventFlow x) =
        compactIntervalOscillationModulusFromEventFlow
          (compactIntervalOscillationModulusToEventFlow y) :=
    congrArg compactIntervalOscillationModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactIntervalOscillationModulusUp,
      compactIntervalOscillationModulusFields x =
        compactIntervalOscillationModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 W1 R1 Q1 O1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 W2 R2 Q2 O2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactIntervalOscillationModulusBHistCarrier :
    BHistCarrier CompactIntervalOscillationModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalOscillationModulusToEventFlow
  fromEventFlow := compactIntervalOscillationModulusFromEventFlow

instance compactIntervalOscillationModulusChapterTasteGate :
    ChapterTasteGate CompactIntervalOscillationModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactIntervalOscillationModulusFromEventFlow
        (compactIntervalOscillationModulusToEventFlow x) = some x
    exact CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_injective heq)

instance compactIntervalOscillationModulusFieldFaithful :
    FieldFaithful CompactIntervalOscillationModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactIntervalOscillationModulusFields
  field_faithful := CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_fields

instance compactIntervalOscillationModulusNontrivial :
    Nontrivial CompactIntervalOscillationModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactIntervalOscillationModulusUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompactIntervalOscillationModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactIntervalOscillationModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactIntervalOscillationModulusUp) ∧
      Nonempty (FieldFaithful CompactIntervalOscillationModulusUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactIntervalOscillationModulusUp) ∧
          (∀ h : BHist,
            compactIntervalOscillationModulusDecodeBHist
              (compactIntervalOscillationModulusEncodeBHist h) = h) ∧
            compactIntervalOscillationModulusEncodeBHist (BHist.e0 BHist.Empty) =
              [BMark.b0] ∧
              (∀ x : CompactIntervalOscillationModulusUp,
                compactIntervalOscillationModulusFromEventFlow
                  (compactIntervalOscillationModulusToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨compactIntervalOscillationModulusChapterTasteGate⟩,
      ⟨compactIntervalOscillationModulusFieldFaithful⟩,
      ⟨compactIntervalOscillationModulusNontrivial⟩,
      CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_decode,
      rfl,
      CompactIntervalOscillationModulusTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.CompactIntervalOscillationModulusUp
