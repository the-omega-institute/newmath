import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RelationalPhysicsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RelationalPhysicsUp : Type where
  | mk (O I L V A H C P N : BHist) : RelationalPhysicsUp
  deriving DecidableEq

def relationalPhysicsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: relationalPhysicsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: relationalPhysicsEncodeBHist h

def relationalPhysicsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (relationalPhysicsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (relationalPhysicsDecodeBHist tail)

private theorem RelationalPhysicsTasteGate_single_carrier_alignment_decode :
    forall h : BHist, relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def relationalPhysicsToEventFlow : RelationalPhysicsUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RelationalPhysicsUp.mk O I L V A H C P N =>
      [[BMark.b0],
        relationalPhysicsEncodeBHist O,
        [BMark.b1, BMark.b0],
        relationalPhysicsEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        relationalPhysicsEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalPhysicsEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalPhysicsEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalPhysicsEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalPhysicsEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        relationalPhysicsEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        relationalPhysicsEncodeBHist N]

private def relationalPhysicsEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => relationalPhysicsEventAtDefault index rest

def relationalPhysicsFromEventFlow (ef : EventFlow) : Option RelationalPhysicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RelationalPhysicsUp.mk
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 1 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 3 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 5 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 7 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 9 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 11 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 13 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 15 ef))
      (relationalPhysicsDecodeBHist (relationalPhysicsEventAtDefault 17 ef)))

private theorem RelationalPhysicsTasteGate_single_carrier_alignment_round_trip :
    forall x : RelationalPhysicsUp,
      relationalPhysicsFromEventFlow (relationalPhysicsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O I L V A H C P N =>
      change
        some
          (RelationalPhysicsUp.mk
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist O))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist I))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist L))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist V))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist A))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist H))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist C))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist P))
            (relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist N))) =
          some (RelationalPhysicsUp.mk O I L V A H C P N)
      rw [RelationalPhysicsTasteGate_single_carrier_alignment_decode O,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode I,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode L,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode V,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode A,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode H,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode C,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode P,
        RelationalPhysicsTasteGate_single_carrier_alignment_decode N]

private theorem RelationalPhysicsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RelationalPhysicsUp} :
    relationalPhysicsToEventFlow x = relationalPhysicsToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      relationalPhysicsFromEventFlow (relationalPhysicsToEventFlow x) =
        relationalPhysicsFromEventFlow (relationalPhysicsToEventFlow y) :=
    congrArg relationalPhysicsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RelationalPhysicsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RelationalPhysicsTasteGate_single_carrier_alignment_round_trip y)))

private def relationalPhysicsFields : RelationalPhysicsUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RelationalPhysicsUp.mk O I L V A H C P N => [O, I, L, V, A, H, C, P, N]

private theorem RelationalPhysicsTasteGate_single_carrier_alignment_fields :
    forall x y : RelationalPhysicsUp,
      relationalPhysicsFields x = relationalPhysicsFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O1 I1 L1 V1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 I2 L2 V2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance relationalPhysicsBHistCarrier : BHistCarrier RelationalPhysicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := relationalPhysicsToEventFlow
  fromEventFlow := relationalPhysicsFromEventFlow

instance relationalPhysicsChapterTasteGate : ChapterTasteGate RelationalPhysicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change relationalPhysicsFromEventFlow (relationalPhysicsToEventFlow x) = some x
    exact RelationalPhysicsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RelationalPhysicsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance relationalPhysicsFieldFaithful : FieldFaithful RelationalPhysicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := relationalPhysicsFields
  field_faithful := RelationalPhysicsTasteGate_single_carrier_alignment_fields

instance relationalPhysicsNontrivial : Nontrivial RelationalPhysicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RelationalPhysicsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RelationalPhysicsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RelationalPhysicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  relationalPhysicsChapterTasteGate

theorem RelationalPhysicsTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RelationalPhysicsUp) ∧
      Nonempty (FieldFaithful RelationalPhysicsUp) ∧
        Nonempty (Nontrivial RelationalPhysicsUp) ∧
          (forall h : BHist, relationalPhysicsDecodeBHist (relationalPhysicsEncodeBHist h) = h) ∧
            (forall x : RelationalPhysicsUp,
              relationalPhysicsFromEventFlow (relationalPhysicsToEventFlow x) = some x) ∧
              (forall x y : RelationalPhysicsUp,
                relationalPhysicsToEventFlow x = relationalPhysicsToEventFlow y -> x = y) ∧
                relationalPhysicsEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨relationalPhysicsChapterTasteGate⟩,
      ⟨relationalPhysicsFieldFaithful⟩,
      ⟨relationalPhysicsNontrivial⟩,
      RelationalPhysicsTasteGate_single_carrier_alignment_decode,
      RelationalPhysicsTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RelationalPhysicsTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RelationalPhysicsUp
