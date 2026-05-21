import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRefutationBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRefutationBoundaryUp : Type where
  | mk (A R D E H C P N botR : BHist) : FiniteRefutationBoundaryUp
  deriving DecidableEq

def finiteRefutationBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRefutationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRefutationBoundaryEncodeBHist h

def finiteRefutationBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRefutationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRefutationBoundaryDecodeBHist tail)

private theorem FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteRefutationBoundaryDecodeBHist
        (finiteRefutationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRefutationBoundaryFields :
    FiniteRefutationBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRefutationBoundaryUp.mk A R D E H C P N botR =>
      [A, R, D, E, H, C, P, N, botR]

def finiteRefutationBoundaryToEventFlow :
    FiniteRefutationBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map finiteRefutationBoundaryEncodeBHist
      (finiteRefutationBoundaryFields x)

def finiteRefutationBoundaryFromEventFlow
    (ef : EventFlow) : Option FiniteRefutationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [A, R, D, E, H, C, P, N, botR] =>
      some
        (FiniteRefutationBoundaryUp.mk
          (finiteRefutationBoundaryDecodeBHist A)
          (finiteRefutationBoundaryDecodeBHist R)
          (finiteRefutationBoundaryDecodeBHist D)
          (finiteRefutationBoundaryDecodeBHist E)
          (finiteRefutationBoundaryDecodeBHist H)
          (finiteRefutationBoundaryDecodeBHist C)
          (finiteRefutationBoundaryDecodeBHist P)
          (finiteRefutationBoundaryDecodeBHist N)
          (finiteRefutationBoundaryDecodeBHist botR))
  | _ => none

private theorem FiniteRefutationBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteRefutationBoundaryUp,
      finiteRefutationBoundaryFromEventFlow
        (finiteRefutationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A R D E H C P N botR =>
      change
        some
          (FiniteRefutationBoundaryUp.mk
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist A))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist R))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist D))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist E))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist H))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist C))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist P))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist N))
            (finiteRefutationBoundaryDecodeBHist
              (finiteRefutationBoundaryEncodeBHist botR))) =
          some (FiniteRefutationBoundaryUp.mk A R D E H C P N botR)
      rw [FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode A,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode R,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode D,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode E,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode H,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode C,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode P,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode N,
        FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode botR]

private theorem FiniteRefutationBoundaryTasteGate_single_carrier_alignment_injective
    {x y : FiniteRefutationBoundaryUp} :
    finiteRefutationBoundaryToEventFlow x =
      finiteRefutationBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRefutationBoundaryFromEventFlow
          (finiteRefutationBoundaryToEventFlow x) =
        finiteRefutationBoundaryFromEventFlow
          (finiteRefutationBoundaryToEventFlow y) :=
    congrArg finiteRefutationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteRefutationBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteRefutationBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteRefutationBoundaryTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteRefutationBoundaryUp,
      finiteRefutationBoundaryFields x = finiteRefutationBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 R1 D1 E1 H1 C1 P1 N1 botR1 =>
      cases y with
      | mk A2 R2 D2 E2 H2 C2 P2 N2 botR2 =>
          cases hfields
          rfl

instance finiteRefutationBoundaryBHistCarrier :
    BHistCarrier FiniteRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRefutationBoundaryToEventFlow
  fromEventFlow := finiteRefutationBoundaryFromEventFlow

instance finiteRefutationBoundaryChapterTasteGate :
    ChapterTasteGate FiniteRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteRefutationBoundaryFromEventFlow
        (finiteRefutationBoundaryToEventFlow x) = some x
    exact FiniteRefutationBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteRefutationBoundaryTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FiniteRefutationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRefutationBoundaryChapterTasteGate

instance finiteRefutationBoundaryFieldFaithful :
    FieldFaithful FiniteRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteRefutationBoundaryFields
  field_faithful := FiniteRefutationBoundaryTasteGate_single_carrier_alignment_fields

instance finiteRefutationBoundaryNontrivial :
    Nontrivial FiniteRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteRefutationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteRefutationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteRefutationBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteRefutationBoundaryDecodeBHist
        (finiteRefutationBoundaryEncodeBHist h) = h) ∧
      (∀ x : FiniteRefutationBoundaryUp,
        finiteRefutationBoundaryToEventFlow x =
          List.map finiteRefutationBoundaryEncodeBHist
            (finiteRefutationBoundaryFields x)) ∧
        (∀ x y : FiniteRefutationBoundaryUp,
          finiteRefutationBoundaryFields x =
            finiteRefutationBoundaryFields y → x = y) ∧
          (∃ x y : FiniteRefutationBoundaryUp, x ≠ y) ∧
            finiteRefutationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FiniteRefutationBoundaryTasteGate_single_carrier_alignment_decode,
      (fun _ => rfl),
      FiniteRefutationBoundaryTasteGate_single_carrier_alignment_fields,
      ⟨FiniteRefutationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        FiniteRefutationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.FiniteRefutationBoundaryUp
