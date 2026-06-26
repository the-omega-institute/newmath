import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaleShapleyStableMatchingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GaleShapleyStableMatchingUp : Type where
  | mk (U V PU PV L T R B M H C Q N : BHist) : GaleShapleyStableMatchingUp
  deriving DecidableEq

def galeShapleyStableMatchingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: galeShapleyStableMatchingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: galeShapleyStableMatchingEncodeBHist h

def galeShapleyStableMatchingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (galeShapleyStableMatchingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (galeShapleyStableMatchingDecodeBHist tail)

private theorem GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def galeShapleyStableMatchingFields : GaleShapleyStableMatchingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GaleShapleyStableMatchingUp.mk U V PU PV L T R B M H C Q N =>
      [U, V, PU, PV, L, T, R, B, M, H, C, Q, N]

def galeShapleyStableMatchingToEventFlow : GaleShapleyStableMatchingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (galeShapleyStableMatchingFields x).map galeShapleyStableMatchingEncodeBHist

private def galeShapleyStableMatchingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => galeShapleyStableMatchingEventAtDefault index rest

def galeShapleyStableMatchingFromEventFlow
    (ef : EventFlow) : Option GaleShapleyStableMatchingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GaleShapleyStableMatchingUp.mk
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 0 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 1 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 2 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 3 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 4 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 5 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 6 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 7 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 8 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 9 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 10 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 11 ef))
      (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEventAtDefault 12 ef)))

private theorem GaleShapleyStableMatchingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GaleShapleyStableMatchingUp,
      galeShapleyStableMatchingFromEventFlow
        (galeShapleyStableMatchingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U V PU PV L T R B M H C Q N =>
      change
        some
          (GaleShapleyStableMatchingUp.mk
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist U))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist V))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist PU))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist PV))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist L))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist T))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist R))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist B))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist M))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist H))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist C))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist Q))
            (galeShapleyStableMatchingDecodeBHist (galeShapleyStableMatchingEncodeBHist N))) =
          some (GaleShapleyStableMatchingUp.mk U V PU PV L T R B M H C Q N)
      rw [GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode U,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode V,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode PU,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode PV,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode L,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode T,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode R,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode B,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode M,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode H,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode C,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode Q,
        GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode N]

private theorem GaleShapleyStableMatchingToEventFlow_injective
    {x y : GaleShapleyStableMatchingUp} :
    galeShapleyStableMatchingToEventFlow x = galeShapleyStableMatchingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      galeShapleyStableMatchingFromEventFlow (galeShapleyStableMatchingToEventFlow x) =
        galeShapleyStableMatchingFromEventFlow (galeShapleyStableMatchingToEventFlow y) :=
    congrArg galeShapleyStableMatchingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GaleShapleyStableMatchingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (GaleShapleyStableMatchingTasteGate_single_carrier_alignment_round_trip y)))

private theorem GaleShapleyStableMatchingTasteGate_single_carrier_alignment_fields :
    ∀ x y : GaleShapleyStableMatchingUp,
      galeShapleyStableMatchingFields x = galeShapleyStableMatchingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 V1 PU1 PV1 L1 T1 R1 B1 M1 H1 C1 Q1 N1 =>
      cases y with
      | mk U2 V2 PU2 PV2 L2 T2 R2 B2 M2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance galeShapleyStableMatchingBHistCarrier : BHistCarrier GaleShapleyStableMatchingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := galeShapleyStableMatchingToEventFlow
  fromEventFlow := galeShapleyStableMatchingFromEventFlow

instance galeShapleyStableMatchingChapterTasteGate :
    ChapterTasteGate GaleShapleyStableMatchingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      galeShapleyStableMatchingFromEventFlow
        (galeShapleyStableMatchingToEventFlow x) = some x
    exact GaleShapleyStableMatchingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GaleShapleyStableMatchingToEventFlow_injective heq)

instance galeShapleyStableMatchingFieldFaithful :
    FieldFaithful GaleShapleyStableMatchingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := galeShapleyStableMatchingFields
  field_faithful := GaleShapleyStableMatchingTasteGate_single_carrier_alignment_fields

instance galeShapleyStableMatchingNontrivial : Nontrivial GaleShapleyStableMatchingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GaleShapleyStableMatchingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      GaleShapleyStableMatchingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem GaleShapleyStableMatchingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GaleShapleyStableMatchingUp) ∧
      Nonempty (FieldFaithful GaleShapleyStableMatchingUp) ∧
        Nonempty (Nontrivial GaleShapleyStableMatchingUp) ∧
          (∀ h : BHist,
            galeShapleyStableMatchingDecodeBHist
              (galeShapleyStableMatchingEncodeBHist h) = h) ∧
            galeShapleyStableMatchingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨galeShapleyStableMatchingChapterTasteGate⟩,
      ⟨galeShapleyStableMatchingFieldFaithful⟩,
      ⟨galeShapleyStableMatchingNontrivial⟩,
      GaleShapleyStableMatchingTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.GaleShapleyStableMatchingUp.TasteGate
