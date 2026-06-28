import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyReflectiveEmbeddingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyReflectiveEmbeddingUp : Type where
  | mk (C S Q D E J H T P N : BHist) : CauchyReflectiveEmbeddingUp
  deriving DecidableEq

def cauchyReflectiveEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyReflectiveEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyReflectiveEmbeddingEncodeBHist h

def cauchyReflectiveEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyReflectiveEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyReflectiveEmbeddingDecodeBHist tail)

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyReflectiveEmbeddingFields :
    CauchyReflectiveEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyReflectiveEmbeddingUp.mk C S Q D E J H T P N =>
      [C, S, Q, D, E, J, H, T, P, N]

def cauchyReflectiveEmbeddingToEventFlow :
    CauchyReflectiveEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyReflectiveEmbeddingFields x).map cauchyReflectiveEmbeddingEncodeBHist

private def cauchyReflectiveEmbeddingEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyReflectiveEmbeddingEventAtDefault index rest

def cauchyReflectiveEmbeddingFromEventFlow
    (ef : EventFlow) : Option CauchyReflectiveEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyReflectiveEmbeddingUp.mk
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 0 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 1 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 2 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 3 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 4 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 5 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 6 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 7 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 8 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (cauchyReflectiveEmbeddingEventAtDefault 9 ef)))

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip
    (x : CauchyReflectiveEmbeddingUp) :
    cauchyReflectiveEmbeddingFromEventFlow
      (cauchyReflectiveEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C S Q D E J H T P N =>
      change
        some
          (CauchyReflectiveEmbeddingUp.mk
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist C))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist S))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist Q))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist D))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist E))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist J))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist H))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist T))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist P))
            (cauchyReflectiveEmbeddingDecodeBHist
              (cauchyReflectiveEmbeddingEncodeBHist N))) =
          some (CauchyReflectiveEmbeddingUp.mk C S Q D E J H T P N)
      rw [CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode C,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode S,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode Q,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode D,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode E,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode J,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode H,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode T,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode P,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode N]

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyReflectiveEmbeddingUp} :
    cauchyReflectiveEmbeddingToEventFlow x =
      cauchyReflectiveEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyReflectiveEmbeddingFromEventFlow
          (cauchyReflectiveEmbeddingToEventFlow x) =
        cauchyReflectiveEmbeddingFromEventFlow
          (cauchyReflectiveEmbeddingToEventFlow y) :=
    congrArg cauchyReflectiveEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyReflectiveEmbeddingUp,
      cauchyReflectiveEmbeddingFields x = cauchyReflectiveEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 S1 Q1 D1 E1 J1 H1 T1 P1 N1 =>
      cases y with
      | mk C2 S2 Q2 D2 E2 J2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance cauchyReflectiveEmbeddingBHistCarrier :
    BHistCarrier CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyReflectiveEmbeddingToEventFlow
  fromEventFlow := cauchyReflectiveEmbeddingFromEventFlow

instance cauchyReflectiveEmbeddingChapterTasteGate :
    ChapterTasteGate CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyReflectiveEmbeddingFromEventFlow
        (cauchyReflectiveEmbeddingToEventFlow x) = some x
    exact CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyReflectiveEmbeddingFieldFaithful :
    FieldFaithful CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyReflectiveEmbeddingFields
  field_faithful := CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_fields

instance cauchyReflectiveEmbeddingNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyReflectiveEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyReflectiveEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment
    (x : CauchyReflectiveEmbeddingUp) :
    BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
      ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · change
      cauchyReflectiveEmbeddingFromEventFlow
        (cauchyReflectiveEmbeddingToEventFlow x) = some x
    exact CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip x
  · exact ⟨BHistCarrier.toEventFlow x, ChapterTasteGate.round_trip x⟩

end BEDC.Derived.CauchyReflectiveEmbeddingUp.TasteGate
