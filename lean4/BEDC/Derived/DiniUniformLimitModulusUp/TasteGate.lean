import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniUniformLimitModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniUniformLimitModulusUp : Type where
  | mk (K F W E Q U L R S H C P N : BHist) : DiniUniformLimitModulusUp
  deriving DecidableEq

def diniUniformLimitModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniUniformLimitModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniUniformLimitModulusEncodeBHist h

def diniUniformLimitModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniUniformLimitModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniUniformLimitModulusDecodeBHist tail)

private theorem DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DiniUniformLimitModulusTasteGate_single_carrier_alignment_fields :
    DiniUniformLimitModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniUniformLimitModulusUp.mk K F W E Q U L R S H C P N =>
      [K, F, W, E, Q, U, L, R, S, H, C, P, N]

def DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow :
    DiniUniformLimitModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (DiniUniformLimitModulusTasteGate_single_carrier_alignment_fields x).map
      diniUniformLimitModulusEncodeBHist

private def DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault index rest

def DiniUniformLimitModulusTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option DiniUniformLimitModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiniUniformLimitModulusUp.mk
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (diniUniformLimitModulusDecodeBHist
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

private theorem DiniUniformLimitModulusTasteGate_single_carrier_alignment_round_trip
    (x : DiniUniformLimitModulusUp) :
    DiniUniformLimitModulusTasteGate_single_carrier_alignment_fromEventFlow
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F W E Q U L R S H C P N =>
      change
        some
          (DiniUniformLimitModulusUp.mk
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist K))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist F))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist W))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist E))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist Q))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist U))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist L))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist R))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist S))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist H))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist C))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist P))
            (diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist N))) =
          some (DiniUniformLimitModulusUp.mk K F W E Q U L R S H C P N)
      rw [DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode K,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode F,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode W,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode E,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode Q,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode U,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode L,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode R,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode S,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode H,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode C,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode P,
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiniUniformLimitModulusUp} :
    DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow x =
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DiniUniformLimitModulusTasteGate_single_carrier_alignment_fromEventFlow
          (DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow x) =
        DiniUniformLimitModulusTasteGate_single_carrier_alignment_fromEventFlow
          (DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DiniUniformLimitModulusTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiniUniformLimitModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DiniUniformLimitModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiniUniformLimitModulusTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DiniUniformLimitModulusUp,
      DiniUniformLimitModulusTasteGate_single_carrier_alignment_fields x =
          DiniUniformLimitModulusTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 W1 E1 Q1 U1 L1 R1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 W2 E2 Q2 U2 L2 R2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance diniUniformLimitModulusBHistCarrier : BHistCarrier DiniUniformLimitModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DiniUniformLimitModulusTasteGate_single_carrier_alignment_fromEventFlow

instance diniUniformLimitModulusChapterTasteGate :
    ChapterTasteGate DiniUniformLimitModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DiniUniformLimitModulusTasteGate_single_carrier_alignment_fromEventFlow
          (DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DiniUniformLimitModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DiniUniformLimitModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance diniUniformLimitModulusFieldFaithful :
    FieldFaithful DiniUniformLimitModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DiniUniformLimitModulusTasteGate_single_carrier_alignment_fields
  field_faithful := DiniUniformLimitModulusTasteGate_single_carrier_alignment_fields_faithful

instance diniUniformLimitModulusNontrivial : Nontrivial DiniUniformLimitModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiniUniformLimitModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DiniUniformLimitModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem DiniUniformLimitModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      diniUniformLimitModulusDecodeBHist (diniUniformLimitModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DiniUniformLimitModulusUp) ∧
        Nonempty (ChapterTasteGate DiniUniformLimitModulusUp) ∧
          Nonempty (FieldFaithful DiniUniformLimitModulusUp) ∧
            Nonempty (Nontrivial DiniUniformLimitModulusUp) ∧
              diniUniformLimitModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DiniUniformLimitModulusTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨diniUniformLimitModulusBHistCarrier⟩,
        ⟨⟨diniUniformLimitModulusChapterTasteGate⟩,
          ⟨⟨diniUniformLimitModulusFieldFaithful⟩,
            ⟨⟨diniUniformLimitModulusNontrivial⟩, rfl⟩⟩⟩⟩⟩

end BEDC.Derived.DiniUniformLimitModulusUp.TasteGate
