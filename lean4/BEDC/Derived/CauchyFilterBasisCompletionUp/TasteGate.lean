import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterBasisCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterBasisCompletionUp : Type where
  | mk (B C W T R L H K P N : BHist) : CauchyFilterBasisCompletionUp
  deriving DecidableEq

def cauchyFilterBasisCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterBasisCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterBasisCompletionEncodeBHist h

def cauchyFilterBasisCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterBasisCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterBasisCompletionDecodeBHist tail)

private theorem cauchyFilterBasisCompletionDecode_encode_bhist :
    ∀ h : BHist,
      cauchyFilterBasisCompletionDecodeBHist
          (cauchyFilterBasisCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterBasisCompletionFields :
    CauchyFilterBasisCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterBasisCompletionUp.mk B C W T R L H K P N =>
      [B, C, W, T, R, L, H, K, P, N]

def cauchyFilterBasisCompletionToEventFlow :
    CauchyFilterBasisCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map cauchyFilterBasisCompletionEncodeBHist
        (cauchyFilterBasisCompletionFields x)

private def cauchyFilterBasisCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterBasisCompletionEventAt index rest

def cauchyFilterBasisCompletionFromEventFlow :
    EventFlow → Option CauchyFilterBasisCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyFilterBasisCompletionUp.mk
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 0 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 1 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 2 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 3 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 4 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 5 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 6 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 7 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 8 ef))
          (cauchyFilterBasisCompletionDecodeBHist
            (cauchyFilterBasisCompletionEventAt 9 ef)))

private theorem cauchyFilterBasisCompletion_round_trip :
    ∀ x : CauchyFilterBasisCompletionUp,
      cauchyFilterBasisCompletionFromEventFlow
          (cauchyFilterBasisCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B C W T R L H K P N =>
      change
        some
          (CauchyFilterBasisCompletionUp.mk
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist B))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist C))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist W))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist T))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist R))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist L))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist H))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist K))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist P))
            (cauchyFilterBasisCompletionDecodeBHist
              (cauchyFilterBasisCompletionEncodeBHist N))) =
          some (CauchyFilterBasisCompletionUp.mk B C W T R L H K P N)
      rw [cauchyFilterBasisCompletionDecode_encode_bhist B,
        cauchyFilterBasisCompletionDecode_encode_bhist C,
        cauchyFilterBasisCompletionDecode_encode_bhist W,
        cauchyFilterBasisCompletionDecode_encode_bhist T,
        cauchyFilterBasisCompletionDecode_encode_bhist R,
        cauchyFilterBasisCompletionDecode_encode_bhist L,
        cauchyFilterBasisCompletionDecode_encode_bhist H,
        cauchyFilterBasisCompletionDecode_encode_bhist K,
        cauchyFilterBasisCompletionDecode_encode_bhist P,
        cauchyFilterBasisCompletionDecode_encode_bhist N]

private theorem cauchyFilterBasisCompletionToEventFlow_injective
    {x y : CauchyFilterBasisCompletionUp} :
    cauchyFilterBasisCompletionToEventFlow x =
        cauchyFilterBasisCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterBasisCompletionFromEventFlow
          (cauchyFilterBasisCompletionToEventFlow x) =
        cauchyFilterBasisCompletionFromEventFlow
          (cauchyFilterBasisCompletionToEventFlow y) :=
    congrArg cauchyFilterBasisCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterBasisCompletion_round_trip x).symm
      (Eq.trans hread (cauchyFilterBasisCompletion_round_trip y)))

private theorem cauchyFilterBasisCompletion_fields_faithful :
    ∀ x y : CauchyFilterBasisCompletionUp,
      cauchyFilterBasisCompletionFields x =
          cauchyFilterBasisCompletionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 C1 W1 T1 R1 L1 H1 K1 P1 N1 =>
      cases y with
      | mk B2 C2 W2 T2 R2 L2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance cauchyFilterBasisCompletionBHistCarrier :
    BHistCarrier CauchyFilterBasisCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterBasisCompletionToEventFlow
  fromEventFlow := cauchyFilterBasisCompletionFromEventFlow

instance cauchyFilterBasisCompletionChapterTasteGate :
    ChapterTasteGate CauchyFilterBasisCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyFilterBasisCompletionFromEventFlow
          (cauchyFilterBasisCompletionToEventFlow x) =
        some x
    exact cauchyFilterBasisCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterBasisCompletionToEventFlow_injective heq)

instance cauchyFilterBasisCompletionFieldFaithful :
    FieldFaithful CauchyFilterBasisCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyFilterBasisCompletionFields
  field_faithful := cauchyFilterBasisCompletion_fields_faithful

instance cauchyFilterBasisCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyFilterBasisCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyFilterBasisCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyFilterBasisCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyFilterBasisCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterBasisCompletionChapterTasteGate

namespace TasteGate

theorem CauchyFilterBasisCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyFilterBasisCompletionDecodeBHist
          (cauchyFilterBasisCompletionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CauchyFilterBasisCompletionUp) ∧
        Nonempty (ChapterTasteGate CauchyFilterBasisCompletionUp) ∧
          cauchyFilterBasisCompletionEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyFilterBasisCompletionDecode_encode_bhist,
      Nonempty.intro cauchyFilterBasisCompletionBHistCarrier,
      Nonempty.intro cauchyFilterBasisCompletionChapterTasteGate,
      rfl⟩

end TasteGate

end BEDC.Derived.CauchyFilterBasisCompletionUp
