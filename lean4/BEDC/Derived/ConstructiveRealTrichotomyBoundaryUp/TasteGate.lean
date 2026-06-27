import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveRealTrichotomyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveRealTrichotomyBoundaryUp : Type where
  | mk (X Y SX SY RX RY D A E L H C P N : BHist) :
      ConstructiveRealTrichotomyBoundaryUp
  deriving DecidableEq

def constructiveRealTrichotomyBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveRealTrichotomyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveRealTrichotomyBoundaryEncodeBHist h

def constructiveRealTrichotomyBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveRealTrichotomyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveRealTrichotomyBoundaryDecodeBHist tail)

private theorem ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveRealTrichotomyBoundaryFields :
    ConstructiveRealTrichotomyBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveRealTrichotomyBoundaryUp.mk X Y SX SY RX RY D A E L H C P N =>
      [X, Y, SX, SY, RX, RY, D, A, E, L, H, C, P, N]

def constructiveRealTrichotomyBoundaryToEventFlow :
    ConstructiveRealTrichotomyBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (constructiveRealTrichotomyBoundaryFields x).map
        constructiveRealTrichotomyBoundaryEncodeBHist

private def constructiveRealTrichotomyBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveRealTrichotomyBoundaryEventAt index rest

def constructiveRealTrichotomyBoundaryFromEventFlow
    (ef : EventFlow) : Option ConstructiveRealTrichotomyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveRealTrichotomyBoundaryUp.mk
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 0 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 1 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 2 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 3 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 4 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 5 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 6 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 7 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 8 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 9 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 10 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 11 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 12 ef))
      (constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEventAt 13 ef)))

private theorem ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveRealTrichotomyBoundaryUp) :
    constructiveRealTrichotomyBoundaryFromEventFlow
      (constructiveRealTrichotomyBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y SX SY RX RY D A E L H C P N =>
      change
        some
          (ConstructiveRealTrichotomyBoundaryUp.mk
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist X))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist Y))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist SX))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist SY))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist RX))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist RY))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist D))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist A))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist E))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist L))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist H))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist C))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist P))
            (constructiveRealTrichotomyBoundaryDecodeBHist
              (constructiveRealTrichotomyBoundaryEncodeBHist N))) =
          some (ConstructiveRealTrichotomyBoundaryUp.mk X Y SX SY RX RY D A E L H C P N)
      rw [ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode X,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode Y,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode SX,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode SY,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode RX,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode RY,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode D,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode A,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode E,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode L,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode H,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode C,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode P,
        ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_fields :
    ∀ x y : ConstructiveRealTrichotomyBoundaryUp,
      constructiveRealTrichotomyBoundaryFields x =
        constructiveRealTrichotomyBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ SX₁ SY₁ RX₁ RY₁ D₁ A₁ E₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ SX₂ SY₂ RX₂ RY₂ D₂ A₂ E₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance constructiveRealTrichotomyBoundaryBHistCarrier :
    BHistCarrier ConstructiveRealTrichotomyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveRealTrichotomyBoundaryToEventFlow
  fromEventFlow := constructiveRealTrichotomyBoundaryFromEventFlow

instance constructiveRealTrichotomyBoundaryFieldFaithful :
    FieldFaithful ConstructiveRealTrichotomyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constructiveRealTrichotomyBoundaryFields
  field_faithful :=
    ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_fields

instance constructiveRealTrichotomyBoundaryChapterTasteGate :
    ChapterTasteGate ConstructiveRealTrichotomyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveRealTrichotomyBoundaryFromEventFlow
        (constructiveRealTrichotomyBoundaryToEventFlow x) = some x
    exact ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    have hread :
        constructiveRealTrichotomyBoundaryFromEventFlow
            (constructiveRealTrichotomyBoundaryToEventFlow x) =
          constructiveRealTrichotomyBoundaryFromEventFlow
            (constructiveRealTrichotomyBoundaryToEventFlow y) :=
      congrArg constructiveRealTrichotomyBoundaryFromEventFlow heq
    exact hxy
      (Option.some.inj
        (Eq.trans
          (ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
          (Eq.trans hread
            (ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_round_trip y))))

instance constructiveRealTrichotomyBoundaryNontrivial :
    Nontrivial ConstructiveRealTrichotomyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstructiveRealTrichotomyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ConstructiveRealTrichotomyBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      constructiveRealTrichotomyBoundaryDecodeBHist
        (constructiveRealTrichotomyBoundaryEncodeBHist h) = h) ∧
      (∀ x : ConstructiveRealTrichotomyBoundaryUp,
        constructiveRealTrichotomyBoundaryFromEventFlow
          (constructiveRealTrichotomyBoundaryToEventFlow x) = some x) ∧
      (∀ x y : ConstructiveRealTrichotomyBoundaryUp,
        constructiveRealTrichotomyBoundaryToEventFlow x =
          constructiveRealTrichotomyBoundaryToEventFlow y → x = y) ∧
      constructiveRealTrichotomyBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        have hread :
            constructiveRealTrichotomyBoundaryFromEventFlow
                (constructiveRealTrichotomyBoundaryToEventFlow x) =
              constructiveRealTrichotomyBoundaryFromEventFlow
                (constructiveRealTrichotomyBoundaryToEventFlow y) :=
          congrArg constructiveRealTrichotomyBoundaryFromEventFlow heq
        exact Option.some.inj
          (Eq.trans
            (ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
            (Eq.trans hread
              (ConstructiveRealTrichotomyBoundaryTasteGate_single_carrier_alignment_round_trip y)))
      · rfl

end BEDC.Derived.ConstructiveRealTrichotomyBoundaryUp
