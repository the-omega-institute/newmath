import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRealUniformModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRealUniformModulusUp : Type where
  | mk (R M U K W A S T C P N : BHist) : CompactRealUniformModulusUp
  deriving DecidableEq

def compactRealUniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRealUniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRealUniformModulusEncodeBHist h

def compactRealUniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRealUniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRealUniformModulusDecodeBHist tail)

private theorem CompactRealUniformModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactRealUniformModulusFields : CompactRealUniformModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealUniformModulusUp.mk R M U K W A S T C P N => [R, M, U, K, W, A, S, T, C, P, N]

def compactRealUniformModulusToEventFlow : CompactRealUniformModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactRealUniformModulusFields x).map compactRealUniformModulusEncodeBHist

private def compactRealUniformModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactRealUniformModulusEventAtDefault index rest

def compactRealUniformModulusFromEventFlow (ef : EventFlow) :
    Option CompactRealUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactRealUniformModulusUp.mk
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 0 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 1 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 2 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 3 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 4 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 5 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 6 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 7 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 8 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 9 ef))
      (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEventAtDefault 10 ef)))

private theorem compactRealUniformModulus_round_trip :
    ∀ x : CompactRealUniformModulusUp,
      compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M U K W A S T C P N =>
      change
        some
            (CompactRealUniformModulusUp.mk
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist R))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist M))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist U))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist K))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist W))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist A))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist S))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist T))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist C))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist P))
              (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist N))) =
          some (CompactRealUniformModulusUp.mk R M U K W A S T C P N)
      rw [CompactRealUniformModulusTasteGate_single_carrier_alignment_decode R,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode M,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode U,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode K,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode W,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode A,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode S,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode T,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode C,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode P,
        CompactRealUniformModulusTasteGate_single_carrier_alignment_decode N]

private theorem compactRealUniformModulusToEventFlow_injective
    {x y : CompactRealUniformModulusUp} :
    compactRealUniformModulusToEventFlow x = compactRealUniformModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow x) =
        compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow y) :=
    congrArg compactRealUniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactRealUniformModulus_round_trip x).symm
      (Eq.trans hread (compactRealUniformModulus_round_trip y)))

instance compactRealUniformModulusBHistCarrier : BHistCarrier CompactRealUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRealUniformModulusToEventFlow
  fromEventFlow := compactRealUniformModulusFromEventFlow

instance compactRealUniformModulusChapterTasteGate :
    ChapterTasteGate CompactRealUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow x) =
      some x
    exact compactRealUniformModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactRealUniformModulusToEventFlow_injective heq)

instance compactRealUniformModulusFieldFaithful :
    FieldFaithful CompactRealUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactRealUniformModulusFields
  field_faithful := by
    intro x y h
    cases x with
    | mk R1 M1 U1 K1 W1 A1 S1 T1 C1 P1 N1 =>
        cases y with
        | mk R2 M2 U2 K2 W2 A2 S2 T2 C2 P2 N2 =>
            cases h
            rfl

def taste_gate : ChapterTasteGate CompactRealUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactRealUniformModulusChapterTasteGate

theorem CompactRealUniformModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist h) = h) ∧
      (∀ x : CompactRealUniformModulusUp,
        compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow x) =
          some x) ∧
        (∀ x y : CompactRealUniformModulusUp,
          compactRealUniformModulusToEventFlow x =
            compactRealUniformModulusToEventFlow y → x = y) ∧
          compactRealUniformModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactRealUniformModulusTasteGate_single_carrier_alignment_decode,
      compactRealUniformModulus_round_trip,
      (fun _ _ heq => compactRealUniformModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactRealUniformModulusUp
