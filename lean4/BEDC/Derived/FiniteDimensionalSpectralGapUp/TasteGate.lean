import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDimensionalSpectralGapUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDimensionalSpectralGapUp : Type where
  | mk (M T V E D R S H C P N : BHist) : FiniteDimensionalSpectralGapUp
  deriving DecidableEq

def finiteDimensionalSpectralGapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDimensionalSpectralGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDimensionalSpectralGapEncodeBHist h

def finiteDimensionalSpectralGapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDimensionalSpectralGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDimensionalSpectralGapDecodeBHist tail)

private theorem FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteDimensionalSpectralGapDecodeBHist
          (finiteDimensionalSpectralGapEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDimensionalSpectralGapFields :
    FiniteDimensionalSpectralGapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalSpectralGapUp.mk M T V E D R S H C P N =>
      [M, T, V, E, D, R, S, H, C, P, N]

def finiteDimensionalSpectralGapToEventFlow :
    FiniteDimensionalSpectralGapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalSpectralGapUp.mk M T V E D R S H C P N =>
      [finiteDimensionalSpectralGapEncodeBHist M,
        finiteDimensionalSpectralGapEncodeBHist T,
        finiteDimensionalSpectralGapEncodeBHist V,
        finiteDimensionalSpectralGapEncodeBHist E,
        finiteDimensionalSpectralGapEncodeBHist D,
        finiteDimensionalSpectralGapEncodeBHist R,
        finiteDimensionalSpectralGapEncodeBHist S,
        finiteDimensionalSpectralGapEncodeBHist H,
        finiteDimensionalSpectralGapEncodeBHist C,
        finiteDimensionalSpectralGapEncodeBHist P,
        finiteDimensionalSpectralGapEncodeBHist N]

private def finiteDimensionalSpectralGapEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteDimensionalSpectralGapEventAt index rest

def finiteDimensionalSpectralGapFromEventFlow :
    EventFlow → Option FiniteDimensionalSpectralGapUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDimensionalSpectralGapUp.mk
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 0 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 1 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 2 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 3 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 4 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 5 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 6 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 7 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 8 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 9 ef))
      (finiteDimensionalSpectralGapDecodeBHist
        (finiteDimensionalSpectralGapEventAt 10 ef)))

private theorem FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteDimensionalSpectralGapUp,
      finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T V E D R S H C P N =>
      change
        some
          (FiniteDimensionalSpectralGapUp.mk
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist M))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist T))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist V))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist E))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist D))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist R))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist S))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist H))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist C))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist P))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist N))) =
          some (FiniteDimensionalSpectralGapUp.mk M T V E D R S H C P N)
      rw [
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode M,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode T,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode V,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode E,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode D,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode R,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode S,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode H,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode C,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode P,
        FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_decode N]

private theorem FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_injective
    {x y : FiniteDimensionalSpectralGapUp} :
    finiteDimensionalSpectralGapToEventFlow x =
        finiteDimensionalSpectralGapToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow x) =
        finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow y) :=
    congrArg finiteDimensionalSpectralGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FiniteDimensionalSpectralGapUp,
      finiteDimensionalSpectralGapFields x = finiteDimensionalSpectralGapFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 T1 V1 E1 D1 R1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 T2 V2 E2 D2 R2 S2 H2 C2 P2 N2 =>
          injection hfields with hM tail0
          injection tail0 with hT tail1
          injection tail1 with hV tail2
          injection tail2 with hE tail3
          injection tail3 with hD tail4
          injection tail4 with hR tail5
          injection tail5 with hS tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hM
          subst hT
          subst hV
          subst hE
          subst hD
          subst hR
          subst hS
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance finiteDimensionalSpectralGapBHistCarrier :
    BHistCarrier FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDimensionalSpectralGapToEventFlow
  fromEventFlow := finiteDimensionalSpectralGapFromEventFlow

instance finiteDimensionalSpectralGapChapterTasteGate :
    ChapterTasteGate FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow x) =
        some x
    exact FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_injective heq)

instance finiteDimensionalSpectralGapFieldFaithful :
    FieldFaithful FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteDimensionalSpectralGapFields
  field_faithful :=
    FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_fields_faithful

instance finiteDimensionalSpectralGapNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteDimensionalSpectralGapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteDimensionalSpectralGapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FiniteDimensionalSpectralGapUp) ∧
      Nonempty (ChapterTasteGate FiniteDimensionalSpectralGapUp) ∧
        (∀ x : FiniteDimensionalSpectralGapUp,
          finiteDimensionalSpectralGapFromEventFlow
              (finiteDimensionalSpectralGapToEventFlow x) =
            some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨finiteDimensionalSpectralGapBHistCarrier⟩,
      ⟨finiteDimensionalSpectralGapChapterTasteGate⟩,
      FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.FiniteDimensionalSpectralGapUp.TasteGate
