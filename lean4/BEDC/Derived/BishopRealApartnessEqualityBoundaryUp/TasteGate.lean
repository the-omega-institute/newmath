import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealApartnessEqualityBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealApartnessEqualityBoundaryUp : Type where
  | mk (R A D S Q T C P N : BHist) : BishopRealApartnessEqualityBoundaryUp
  deriving DecidableEq

def bishopRealApartnessEqualityBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealApartnessEqualityBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealApartnessEqualityBoundaryEncodeBHist h

def bishopRealApartnessEqualityBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealApartnessEqualityBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealApartnessEqualityBoundaryDecodeBHist tail)

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealApartnessEqualityBoundaryFields :
    BishopRealApartnessEqualityBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealApartnessEqualityBoundaryUp.mk R A D S Q T C P N =>
      [R, A, D, S, Q, T, C, P, N]

def bishopRealApartnessEqualityBoundaryToEventFlow :
    BishopRealApartnessEqualityBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopRealApartnessEqualityBoundaryFields x).map
      bishopRealApartnessEqualityBoundaryEncodeBHist

private def bishopRealApartnessEqualityBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopRealApartnessEqualityBoundaryEventAtDefault index rest

def bishopRealApartnessEqualityBoundaryFromEventFlow
    (ef : EventFlow) : Option BishopRealApartnessEqualityBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealApartnessEqualityBoundaryUp.mk
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 0 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 1 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 2 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 3 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 4 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 5 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 6 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 7 ef))
      (bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEventAtDefault 8 ef)))

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRealApartnessEqualityBoundaryUp,
      bishopRealApartnessEqualityBoundaryFromEventFlow
        (bishopRealApartnessEqualityBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A D S Q T C P N =>
      change
        some
          (BishopRealApartnessEqualityBoundaryUp.mk
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist R))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist A))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist D))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist S))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist Q))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist T))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist C))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist P))
            (bishopRealApartnessEqualityBoundaryDecodeBHist
              (bishopRealApartnessEqualityBoundaryEncodeBHist N))) =
          some (BishopRealApartnessEqualityBoundaryUp.mk R A D S Q T C P N)
      rw [BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode R,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode A,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode D,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode S,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode Q,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode T,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode C,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode P,
        BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopRealApartnessEqualityBoundaryUp,
      bishopRealApartnessEqualityBoundaryFields x =
        bishopRealApartnessEqualityBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R A D S Q T C P N =>
      cases y with
      | mk R' A' D' S' Q' T' C' P' N' =>
          injection hfields with hR htail0
          injection htail0 with hA htail1
          injection htail1 with hD htail2
          injection htail2 with hS htail3
          injection htail3 with hQ htail4
          injection htail4 with hT htail5
          injection htail5 with hC htail6
          injection htail6 with hP htail7
          injection htail7 with hN _hNil
          cases hR
          cases hA
          cases hD
          cases hS
          cases hQ
          cases hT
          cases hC
          cases hP
          cases hN
          rfl

private theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealApartnessEqualityBoundaryUp} :
    bishopRealApartnessEqualityBoundaryToEventFlow x =
      bishopRealApartnessEqualityBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealApartnessEqualityBoundaryFromEventFlow
          (bishopRealApartnessEqualityBoundaryToEventFlow x) =
        bishopRealApartnessEqualityBoundaryFromEventFlow
          (bishopRealApartnessEqualityBoundaryToEventFlow y) :=
    congrArg bishopRealApartnessEqualityBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRealApartnessEqualityBoundaryBHistCarrier :
    BHistCarrier BishopRealApartnessEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealApartnessEqualityBoundaryToEventFlow
  fromEventFlow := bishopRealApartnessEqualityBoundaryFromEventFlow

instance bishopRealApartnessEqualityBoundaryChapterTasteGate :
    ChapterTasteGate BishopRealApartnessEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRealApartnessEqualityBoundaryFromEventFlow
        (bishopRealApartnessEqualityBoundaryToEventFlow x) = some x
    exact BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance bishopRealApartnessEqualityBoundaryFieldFaithful :
    FieldFaithful BishopRealApartnessEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRealApartnessEqualityBoundaryFields
  field_faithful := BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate BishopRealApartnessEqualityBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRealApartnessEqualityBoundaryChapterTasteGate

theorem BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRealApartnessEqualityBoundaryDecodeBHist
        (bishopRealApartnessEqualityBoundaryEncodeBHist h) = h) ∧
      (∀ x : BishopRealApartnessEqualityBoundaryUp,
        bishopRealApartnessEqualityBoundaryFromEventFlow
          (bishopRealApartnessEqualityBoundaryToEventFlow x) = some x) ∧
        (∀ x y : BishopRealApartnessEqualityBoundaryUp,
          bishopRealApartnessEqualityBoundaryToEventFlow x =
            bishopRealApartnessEqualityBoundaryToEventFlow y → x = y) ∧
          bishopRealApartnessEqualityBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          BishopRealApartnessEqualityBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.BishopRealApartnessEqualityBoundaryUp
