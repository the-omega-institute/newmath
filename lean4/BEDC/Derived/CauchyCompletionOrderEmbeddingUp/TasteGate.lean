import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionOrderEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionOrderEmbeddingUp : Type where
  | mk (K L W D R E T C P N : BHist) : CauchyCompletionOrderEmbeddingUp
  deriving DecidableEq

def cauchyCompletionOrderEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionOrderEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionOrderEmbeddingEncodeBHist h

def cauchyCompletionOrderEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionOrderEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionOrderEmbeddingDecodeBHist tail)

private theorem CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionOrderEmbeddingDecodeBHist
          (cauchyCompletionOrderEmbeddingEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionOrderEmbeddingFields :
    CauchyCompletionOrderEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionOrderEmbeddingUp.mk K L W D R E T C P N =>
      [K, L, W, D, R, E, T, C, P, N]

def cauchyCompletionOrderEmbeddingToEventFlow :
    CauchyCompletionOrderEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionOrderEmbeddingFields x).map
      cauchyCompletionOrderEmbeddingEncodeBHist

private def cauchyCompletionOrderEmbeddingEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionOrderEmbeddingEventAtDefault index rest

def cauchyCompletionOrderEmbeddingFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionOrderEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionOrderEmbeddingUp.mk
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 0 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 1 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 2 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 3 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 4 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 5 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 6 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 7 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 8 ef))
      (cauchyCompletionOrderEmbeddingDecodeBHist
        (cauchyCompletionOrderEmbeddingEventAtDefault 9 ef)))

private theorem CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionOrderEmbeddingUp,
      cauchyCompletionOrderEmbeddingFromEventFlow
          (cauchyCompletionOrderEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K L W D R E T C P N =>
      change
        some
          (CauchyCompletionOrderEmbeddingUp.mk
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist K))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist L))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist W))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist D))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist R))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist E))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist T))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist C))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist P))
            (cauchyCompletionOrderEmbeddingDecodeBHist
              (cauchyCompletionOrderEmbeddingEncodeBHist N))) =
          some (CauchyCompletionOrderEmbeddingUp.mk K L W D R E T C P N)
      rw [CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode K,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode L,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode W,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode R,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode T,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_injective
    {x y : CauchyCompletionOrderEmbeddingUp} :
    cauchyCompletionOrderEmbeddingToEventFlow x =
      cauchyCompletionOrderEmbeddingToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionOrderEmbeddingFromEventFlow
          (cauchyCompletionOrderEmbeddingToEventFlow x) =
        cauchyCompletionOrderEmbeddingFromEventFlow
          (cauchyCompletionOrderEmbeddingToEventFlow y) :=
    congrArg cauchyCompletionOrderEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyCompletionOrderEmbeddingUp,
      cauchyCompletionOrderEmbeddingFields x =
        cauchyCompletionOrderEmbeddingFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 L1 W1 D1 R1 E1 T1 C1 P1 N1 =>
      cases y with
      | mk K2 L2 W2 D2 R2 E2 T2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletionOrderEmbeddingBHistCarrier :
    BHistCarrier CauchyCompletionOrderEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionOrderEmbeddingToEventFlow
  fromEventFlow := cauchyCompletionOrderEmbeddingFromEventFlow

instance cauchyCompletionOrderEmbeddingChapterTasteGate :
    ChapterTasteGate CauchyCompletionOrderEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionOrderEmbeddingFromEventFlow
          (cauchyCompletionOrderEmbeddingToEventFlow x) =
        some x
    exact CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_injective heq)

instance cauchyCompletionOrderEmbeddingFieldFaithful :
    FieldFaithful CauchyCompletionOrderEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionOrderEmbeddingFields
  field_faithful :=
    CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_fields

instance cauchyCompletionOrderEmbeddingNontrivial :
    Nontrivial CauchyCompletionOrderEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionOrderEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyCompletionOrderEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionOrderEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionOrderEmbeddingChapterTasteGate

theorem CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionOrderEmbeddingDecodeBHist
          (cauchyCompletionOrderEmbeddingEncodeBHist h) =
        h) ∧
      (∀ x : CauchyCompletionOrderEmbeddingUp,
        cauchyCompletionOrderEmbeddingFromEventFlow
            (cauchyCompletionOrderEmbeddingToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyCompletionOrderEmbeddingUp,
          cauchyCompletionOrderEmbeddingToEventFlow x =
            cauchyCompletionOrderEmbeddingToEventFlow y →
          x = y) ∧
          cauchyCompletionOrderEmbeddingEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_decode,
      CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionOrderEmbeddingTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionOrderEmbeddingUp
