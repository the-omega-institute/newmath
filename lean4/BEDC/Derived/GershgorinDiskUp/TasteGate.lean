import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GershgorinDiskUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GershgorinDiskUp : Type where
  | mk (M R D B H C P N : BHist) : GershgorinDiskUp
  deriving DecidableEq

def gershgorinDiskEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gershgorinDiskEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gershgorinDiskEncodeBHist h

def gershgorinDiskDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gershgorinDiskDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gershgorinDiskDecodeBHist tail)

private theorem GershgorinDiskUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gershgorinDiskToEventFlow : GershgorinDiskUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GershgorinDiskUp.mk M R D B H C P N =>
      [[BMark.b0],
        gershgorinDiskEncodeBHist M,
        [BMark.b1, BMark.b0],
        gershgorinDiskEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        gershgorinDiskEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gershgorinDiskEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gershgorinDiskEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gershgorinDiskEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gershgorinDiskEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        gershgorinDiskEncodeBHist N]

private def gershgorinDiskEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => gershgorinDiskEventAtDefault index rest

def gershgorinDiskFromEventFlow (ef : EventFlow) : Option GershgorinDiskUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GershgorinDiskUp.mk
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 1 ef))
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 3 ef))
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 5 ef))
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 7 ef))
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 9 ef))
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 11 ef))
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 13 ef))
      (gershgorinDiskDecodeBHist (gershgorinDiskEventAtDefault 15 ef)))

private theorem GershgorinDiskUpTasteGate_single_carrier_alignment_round_trip :
    forall x : GershgorinDiskUp,
      gershgorinDiskFromEventFlow (gershgorinDiskToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R D B H C P N =>
      change
        some
          (GershgorinDiskUp.mk
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist M))
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist R))
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist D))
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist B))
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist H))
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist C))
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist P))
            (gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist N))) =
          some (GershgorinDiskUp.mk M R D B H C P N)
      rw [GershgorinDiskUpTasteGate_single_carrier_alignment_decode M,
        GershgorinDiskUpTasteGate_single_carrier_alignment_decode R,
        GershgorinDiskUpTasteGate_single_carrier_alignment_decode D,
        GershgorinDiskUpTasteGate_single_carrier_alignment_decode B,
        GershgorinDiskUpTasteGate_single_carrier_alignment_decode H,
        GershgorinDiskUpTasteGate_single_carrier_alignment_decode C,
        GershgorinDiskUpTasteGate_single_carrier_alignment_decode P,
        GershgorinDiskUpTasteGate_single_carrier_alignment_decode N]

private theorem GershgorinDiskUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GershgorinDiskUp} :
    gershgorinDiskToEventFlow x = gershgorinDiskToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gershgorinDiskFromEventFlow (gershgorinDiskToEventFlow x) =
        gershgorinDiskFromEventFlow (gershgorinDiskToEventFlow y) :=
    congrArg gershgorinDiskFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GershgorinDiskUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GershgorinDiskUpTasteGate_single_carrier_alignment_round_trip y)))

private def gershgorinDiskFields : GershgorinDiskUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GershgorinDiskUp.mk M R D B H C P N => [M, R, D, B, H, C, P, N]

private theorem GershgorinDiskUpTasteGate_single_carrier_alignment_fields :
    forall x y : GershgorinDiskUp, gershgorinDiskFields x = gershgorinDiskFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 R1 D1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 R2 D2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance gershgorinDiskBHistCarrier : BHistCarrier GershgorinDiskUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gershgorinDiskToEventFlow
  fromEventFlow := gershgorinDiskFromEventFlow

instance gershgorinDiskChapterTasteGate : ChapterTasteGate GershgorinDiskUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gershgorinDiskFromEventFlow (gershgorinDiskToEventFlow x) = some x
    exact GershgorinDiskUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GershgorinDiskUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance gershgorinDiskFieldFaithful : FieldFaithful GershgorinDiskUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gershgorinDiskFields
  field_faithful := GershgorinDiskUpTasteGate_single_carrier_alignment_fields

instance gershgorinDiskNontrivial : Nontrivial GershgorinDiskUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GershgorinDiskUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      GershgorinDiskUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GershgorinDiskUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gershgorinDiskChapterTasteGate

theorem GershgorinDiskUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GershgorinDiskUp) ∧
      Nonempty (FieldFaithful GershgorinDiskUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial GershgorinDiskUp) ∧
          (∀ h : BHist, gershgorinDiskDecodeBHist (gershgorinDiskEncodeBHist h) = h) ∧
            (∀ x : GershgorinDiskUp,
              gershgorinDiskFromEventFlow (gershgorinDiskToEventFlow x) = some x) ∧
              (∀ x y : GershgorinDiskUp,
                gershgorinDiskToEventFlow x = gershgorinDiskToEventFlow y -> x = y) ∧
                gershgorinDiskEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨gershgorinDiskChapterTasteGate⟩,
      ⟨gershgorinDiskFieldFaithful⟩,
      ⟨gershgorinDiskNontrivial⟩,
      GershgorinDiskUpTasteGate_single_carrier_alignment_decode,
      GershgorinDiskUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => GershgorinDiskUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.GershgorinDiskUp
