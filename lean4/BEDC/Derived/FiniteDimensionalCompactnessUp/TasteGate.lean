import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDimensionalCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDimensionalCompactnessUp : Type where
  | mk (V M R E N I F W S H C P Q : BHist) : FiniteDimensionalCompactnessUp
  deriving DecidableEq

def finiteDimensionalCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDimensionalCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDimensionalCompactnessEncodeBHist h

def finiteDimensionalCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDimensionalCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDimensionalCompactnessDecodeBHist tail)

private theorem FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDimensionalCompactnessFields :
    FiniteDimensionalCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalCompactnessUp.mk V M R E N I F W S H C P Q =>
      [V, M, R, E, N, I, F, W, S, H, C, P, Q]

def finiteDimensionalCompactnessToEventFlow :
    FiniteDimensionalCompactnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (finiteDimensionalCompactnessFields x).map finiteDimensionalCompactnessEncodeBHist

private def finiteDimensionalCompactnessEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteDimensionalCompactnessEventAtDefault index rest

def finiteDimensionalCompactnessFromEventFlow
    (ef : EventFlow) : Option FiniteDimensionalCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDimensionalCompactnessUp.mk
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 0 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 1 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 2 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 3 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 4 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 5 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 6 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 7 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 8 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 9 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 10 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 11 ef))
      (finiteDimensionalCompactnessDecodeBHist
        (finiteDimensionalCompactnessEventAtDefault 12 ef)))

private theorem FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteDimensionalCompactnessUp,
      finiteDimensionalCompactnessFromEventFlow
        (finiteDimensionalCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V M R E N I F W S H C P Q =>
      change
        some
          (FiniteDimensionalCompactnessUp.mk
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist V))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist M))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist R))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist E))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist N))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist I))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist F))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist W))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist S))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist H))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist C))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist P))
            (finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist Q))) =
          some (FiniteDimensionalCompactnessUp.mk V M R E N I F W S H C P Q)
      rw [FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode V,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode M,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode R,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode E,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode N,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode I,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode F,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode W,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode S,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode H,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode C,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode P,
        FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode Q]

private theorem FiniteDimensionalCompactnessToEventFlow_injective
    {x y : FiniteDimensionalCompactnessUp} :
    finiteDimensionalCompactnessToEventFlow x =
      finiteDimensionalCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDimensionalCompactnessFromEventFlow
          (finiteDimensionalCompactnessToEventFlow x) =
        finiteDimensionalCompactnessFromEventFlow
          (finiteDimensionalCompactnessToEventFlow y) :=
    congrArg finiteDimensionalCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteDimensionalCompactnessUp,
      finiteDimensionalCompactnessFields x = finiteDimensionalCompactnessFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V1 M1 R1 E1 N1 I1 F1 W1 S1 H1 C1 P1 Q1 =>
      cases y with
      | mk V2 M2 R2 E2 N2 I2 F2 W2 S2 H2 C2 P2 Q2 =>
          cases hfields
          rfl

instance finiteDimensionalCompactnessBHistCarrier :
    BHistCarrier FiniteDimensionalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDimensionalCompactnessToEventFlow
  fromEventFlow := finiteDimensionalCompactnessFromEventFlow

instance finiteDimensionalCompactnessChapterTasteGate :
    ChapterTasteGate FiniteDimensionalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteDimensionalCompactnessFromEventFlow
        (finiteDimensionalCompactnessToEventFlow x) = some x
    exact FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteDimensionalCompactnessToEventFlow_injective heq)

instance finiteDimensionalCompactnessFieldFaithful :
    FieldFaithful FiniteDimensionalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteDimensionalCompactnessFields
  field_faithful := FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_fields

instance finiteDimensionalCompactnessNontrivial :
    Nontrivial FiniteDimensionalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteDimensionalCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteDimensionalCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteDimensionalCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteDimensionalCompactnessChapterTasteGate

theorem FiniteDimensionalCompactnessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteDimensionalCompactnessUp) ∧
      Nonempty (FieldFaithful FiniteDimensionalCompactnessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteDimensionalCompactnessUp) ∧
          (∀ h : BHist,
            finiteDimensionalCompactnessDecodeBHist
              (finiteDimensionalCompactnessEncodeBHist h) = h) ∧
            (∀ x : FiniteDimensionalCompactnessUp,
              finiteDimensionalCompactnessFromEventFlow
                (finiteDimensionalCompactnessToEventFlow x) = some x) ∧
              finiteDimensionalCompactnessEncodeBHist BHist.Empty =
                ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨finiteDimensionalCompactnessChapterTasteGate⟩,
      ⟨finiteDimensionalCompactnessFieldFaithful⟩,
      ⟨finiteDimensionalCompactnessNontrivial⟩,
      FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_decode,
      FiniteDimensionalCompactnessTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.FiniteDimensionalCompactnessUp
