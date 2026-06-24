import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyWindowExhaustionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyWindowExhaustionUp : Type where
  | mk (S T D R E H C P N : BHist) : UniformCauchyWindowExhaustionUp
  deriving DecidableEq

def uniformCauchyWindowExhaustionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyWindowExhaustionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyWindowExhaustionEncodeBHist h

def uniformCauchyWindowExhaustionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyWindowExhaustionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyWindowExhaustionDecodeBHist tail)

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      uniformCauchyWindowExhaustionDecodeBHist
          (uniformCauchyWindowExhaustionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def uniformCauchyWindowExhaustionFields :
    UniformCauchyWindowExhaustionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyWindowExhaustionUp.mk S T D R E H C P N => [S, T, D, R, E, H, C, P, N]

def uniformCauchyWindowExhaustionToEventFlow : UniformCauchyWindowExhaustionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformCauchyWindowExhaustionFields x).map uniformCauchyWindowExhaustionEncodeBHist

private def uniformCauchyWindowExhaustionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformCauchyWindowExhaustionEventAtDefault index rest

def uniformCauchyWindowExhaustionFromEventFlow
    (ef : EventFlow) : Option UniformCauchyWindowExhaustionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchyWindowExhaustionUp.mk
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 0 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 1 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 2 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 3 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 4 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 5 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 6 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 7 ef))
      (uniformCauchyWindowExhaustionDecodeBHist
        (uniformCauchyWindowExhaustionEventAtDefault 8 ef)))

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip :
    forall x : UniformCauchyWindowExhaustionUp,
      uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T D R E H C P N =>
      change
        some
          (UniformCauchyWindowExhaustionUp.mk
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist S))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist T))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist D))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist R))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist E))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist H))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist C))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist P))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist N))) =
          some (UniformCauchyWindowExhaustionUp.mk S T D R E H C P N)
      rw [UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode S,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode T,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode D,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode R,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode E,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode H,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode C,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode P,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode N]

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCauchyWindowExhaustionUp} :
    uniformCauchyWindowExhaustionToEventFlow x =
        uniformCauchyWindowExhaustionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow x) =
        uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow y) :=
    congrArg uniformCauchyWindowExhaustionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_fields :
    forall x y : UniformCauchyWindowExhaustionUp,
      uniformCauchyWindowExhaustionFields x = uniformCauchyWindowExhaustionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformCauchyWindowExhaustionBHistCarrier :
    BHistCarrier UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyWindowExhaustionToEventFlow
  fromEventFlow := uniformCauchyWindowExhaustionFromEventFlow

instance uniformCauchyWindowExhaustionChapterTasteGate :
    ChapterTasteGate UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow x) =
        some x
    exact UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformCauchyWindowExhaustionFieldFaithful :
    FieldFaithful UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCauchyWindowExhaustionFields
  field_faithful := UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_fields

instance uniformCauchyWindowExhaustionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCauchyWindowExhaustionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCauchyWindowExhaustionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformCauchyWindowExhaustionUp) ∧
      Nonempty (FieldFaithful UniformCauchyWindowExhaustionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial UniformCauchyWindowExhaustionUp) ∧
      (∀ h : BHist,
        uniformCauchyWindowExhaustionDecodeBHist
            (uniformCauchyWindowExhaustionEncodeBHist h) =
          h) ∧
      (∀ x : UniformCauchyWindowExhaustionUp,
        uniformCauchyWindowExhaustionFromEventFlow
            (uniformCauchyWindowExhaustionToEventFlow x) =
          some x) ∧
      (∀ x y : UniformCauchyWindowExhaustionUp,
        uniformCauchyWindowExhaustionToEventFlow x =
            uniformCauchyWindowExhaustionToEventFlow y ->
          x = y) ∧
      uniformCauchyWindowExhaustionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨uniformCauchyWindowExhaustionChapterTasteGate⟩,
      ⟨uniformCauchyWindowExhaustionFieldFaithful⟩,
      ⟨uniformCauchyWindowExhaustionNontrivial⟩,
      UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode,
      UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformCauchyWindowExhaustionUp.TasteGate
