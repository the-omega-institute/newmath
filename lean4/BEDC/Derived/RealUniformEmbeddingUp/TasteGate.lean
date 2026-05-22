import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformEmbeddingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformEmbeddingUp : Type where
  | mk (S W D Q E U H C P N : BHist) : RealUniformEmbeddingUp
  deriving DecidableEq

def realUniformEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformEmbeddingEncodeBHist h

def realUniformEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformEmbeddingDecodeBHist tail)

theorem RealUniformEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformEmbeddingToEventFlow : RealUniformEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEmbeddingUp.mk S W D Q E U H C P N =>
      [realUniformEmbeddingEncodeBHist S,
        realUniformEmbeddingEncodeBHist W,
        realUniformEmbeddingEncodeBHist D,
        realUniformEmbeddingEncodeBHist Q,
        realUniformEmbeddingEncodeBHist E,
        realUniformEmbeddingEncodeBHist U,
        realUniformEmbeddingEncodeBHist H,
        realUniformEmbeddingEncodeBHist C,
        realUniformEmbeddingEncodeBHist P,
        realUniformEmbeddingEncodeBHist N]

def realUniformEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realUniformEmbeddingEventAtDefault index rest

def realUniformEmbeddingFromEventFlow (ef : EventFlow) : Option RealUniformEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealUniformEmbeddingUp.mk
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 0 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 1 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 2 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 3 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 4 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 5 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 6 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 7 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 8 ef))
      (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEventAtDefault 9 ef)))

theorem RealUniformEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealUniformEmbeddingUp,
      realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D Q E U H C P N =>
      change
        some
          (RealUniformEmbeddingUp.mk
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist S))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist W))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist D))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist Q))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist E))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist U))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist H))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist C))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist P))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist N))) =
          some (RealUniformEmbeddingUp.mk S W D Q E U H C P N)
      rw [RealUniformEmbeddingTasteGate_single_carrier_alignment_decode S,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode W,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode D,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode Q,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode E,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode U,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode H,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode C,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode P,
        RealUniformEmbeddingTasteGate_single_carrier_alignment_decode N]

theorem RealUniformEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealUniformEmbeddingUp} :
    realUniformEmbeddingToEventFlow x = realUniformEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) =
        realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow y) :=
    congrArg realUniformEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealUniformEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealUniformEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

def realUniformEmbeddingFields : RealUniformEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEmbeddingUp.mk S W D Q E U H C P N => [S, W, D, Q, E, U, H, C, P, N]

theorem RealUniformEmbeddingTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealUniformEmbeddingUp, realUniformEmbeddingFields x = realUniformEmbeddingFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 D1 Q1 E1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 D2 Q2 E2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realUniformEmbeddingBHistCarrier : BHistCarrier RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformEmbeddingToEventFlow
  fromEventFlow := realUniformEmbeddingFromEventFlow

instance realUniformEmbeddingChapterTasteGate : ChapterTasteGate RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x
    exact RealUniformEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealUniformEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realUniformEmbeddingFieldFaithful : FieldFaithful RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformEmbeddingFields
  field_faithful := RealUniformEmbeddingTasteGate_single_carrier_alignment_fields

instance realUniformEmbeddingNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformEmbeddingChapterTasteGate

theorem RealUniformEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealUniformEmbeddingUp) ∧
      Nonempty (FieldFaithful RealUniformEmbeddingUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealUniformEmbeddingUp) ∧
          (∀ h : BHist, realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist h) = h) ∧
            (∀ x : RealUniformEmbeddingUp,
              realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x) ∧
              (∀ x y : RealUniformEmbeddingUp,
                realUniformEmbeddingToEventFlow x = realUniformEmbeddingToEventFlow y → x = y) ∧
                realUniformEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨realUniformEmbeddingChapterTasteGate⟩,
      ⟨realUniformEmbeddingFieldFaithful⟩,
      ⟨realUniformEmbeddingNontrivial⟩,
      RealUniformEmbeddingTasteGate_single_carrier_alignment_decode,
      RealUniformEmbeddingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealUniformEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealUniformEmbeddingUp.TasteGate
