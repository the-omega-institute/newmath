import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundaryOrbitInventoryPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundaryOrbitInventoryPolynomialUp : Type where
  | mk (O K E M H C P N : BHist) : BoundaryOrbitInventoryPolynomialUp
  deriving DecidableEq

def boundaryOrbitInventoryPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundaryOrbitInventoryPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundaryOrbitInventoryPolynomialEncodeBHist h

def boundaryOrbitInventoryPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundaryOrbitInventoryPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundaryOrbitInventoryPolynomialDecodeBHist tail)

private theorem BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundaryOrbitInventoryPolynomialDecodeBHist
        (boundaryOrbitInventoryPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundaryOrbitInventoryPolynomialFields :
    BoundaryOrbitInventoryPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundaryOrbitInventoryPolynomialUp.mk O K E M H C P N => [O, K, E, M, H, C, P, N]

def boundaryOrbitInventoryPolynomialToEventFlow :
    BoundaryOrbitInventoryPolynomialUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundaryOrbitInventoryPolynomialFields x).map
      boundaryOrbitInventoryPolynomialEncodeBHist

private def boundaryOrbitInventoryPolynomialRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => boundaryOrbitInventoryPolynomialRawAt n rest

def boundaryOrbitInventoryPolynomialFromEventFlow :
    EventFlow → Option BoundaryOrbitInventoryPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (BoundaryOrbitInventoryPolynomialUp.mk
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 0 flow))
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 1 flow))
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 2 flow))
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 3 flow))
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 4 flow))
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 5 flow))
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 6 flow))
        (boundaryOrbitInventoryPolynomialDecodeBHist
          (boundaryOrbitInventoryPolynomialRawAt 7 flow)))

private theorem BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_round_trip
    (x : BoundaryOrbitInventoryPolynomialUp) :
    boundaryOrbitInventoryPolynomialFromEventFlow
      (boundaryOrbitInventoryPolynomialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O K E M H C P N =>
      change
        some
            (BoundaryOrbitInventoryPolynomialUp.mk
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist O))
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist K))
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist E))
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist M))
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist H))
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist C))
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist P))
              (boundaryOrbitInventoryPolynomialDecodeBHist
                (boundaryOrbitInventoryPolynomialEncodeBHist N))) =
          some (BoundaryOrbitInventoryPolynomialUp.mk O K E M H C P N)
      rw [BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode O,
        BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode K,
        BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode E,
        BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode M,
        BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode H,
        BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode C,
        BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode P,
        BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_decode N]

private theorem BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_injective
    {x y : BoundaryOrbitInventoryPolynomialUp} :
    boundaryOrbitInventoryPolynomialToEventFlow x =
      boundaryOrbitInventoryPolynomialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundaryOrbitInventoryPolynomialFromEventFlow
          (boundaryOrbitInventoryPolynomialToEventFlow x) =
        boundaryOrbitInventoryPolynomialFromEventFlow
          (boundaryOrbitInventoryPolynomialToEventFlow y) :=
    congrArg boundaryOrbitInventoryPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_fields :
    ∀ x y : BoundaryOrbitInventoryPolynomialUp,
      boundaryOrbitInventoryPolynomialFields x =
        boundaryOrbitInventoryPolynomialFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ K₁ E₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ K₂ E₂ M₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance boundaryOrbitInventoryPolynomialBHistCarrier :
    BHistCarrier BoundaryOrbitInventoryPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundaryOrbitInventoryPolynomialToEventFlow
  fromEventFlow := boundaryOrbitInventoryPolynomialFromEventFlow

instance boundaryOrbitInventoryPolynomialChapterTasteGate :
    ChapterTasteGate BoundaryOrbitInventoryPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundaryOrbitInventoryPolynomialFromEventFlow
        (boundaryOrbitInventoryPolynomialToEventFlow x) = some x
    exact BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_injective heq)

instance boundaryOrbitInventoryPolynomialFieldFaithful :
    FieldFaithful BoundaryOrbitInventoryPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundaryOrbitInventoryPolynomialFields
  field_faithful := BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment_fields

instance boundaryOrbitInventoryPolynomialNontrivial :
    Nontrivial BoundaryOrbitInventoryPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundaryOrbitInventoryPolynomialUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundaryOrbitInventoryPolynomialUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem BoundaryOrbitInventoryPolynomialTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BoundaryOrbitInventoryPolynomialUp) ∧
      Nonempty (ChapterTasteGate BoundaryOrbitInventoryPolynomialUp) ∧
        Nonempty (FieldFaithful BoundaryOrbitInventoryPolynomialUp) ∧
          Nonempty (Nontrivial BoundaryOrbitInventoryPolynomialUp) ∧
            boundaryOrbitInventoryPolynomialFields
                (BoundaryOrbitInventoryPolynomialUp.mk BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty] ∧
              BoundaryOrbitInventoryPolynomialUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ≠
                BoundaryOrbitInventoryPolynomialUp.mk (BHist.e0 BHist.Empty)
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨boundaryOrbitInventoryPolynomialBHistCarrier⟩,
      ⟨⟨boundaryOrbitInventoryPolynomialChapterTasteGate⟩,
        ⟨⟨boundaryOrbitInventoryPolynomialFieldFaithful⟩,
          ⟨⟨boundaryOrbitInventoryPolynomialNontrivial⟩,
            ⟨rfl, by
              intro h
              cases h⟩⟩⟩⟩⟩

end BEDC.Derived.BoundaryOrbitInventoryPolynomialUp
