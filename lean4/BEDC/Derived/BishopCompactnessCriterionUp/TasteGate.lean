import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompactnessCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompactnessCriterionUp : Type where
  | mk (M T F C L Q H R P N : BHist) : BishopCompactnessCriterionUp
  deriving DecidableEq

def bishopCompactnessCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompactnessCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompactnessCriterionEncodeBHist h

def bishopCompactnessCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompactnessCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompactnessCriterionDecodeBHist tail)

private theorem BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompactnessCriterionFields :
    BishopCompactnessCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompactnessCriterionUp.mk M T F C L Q H R P N => [M, T, F, C, L, Q, H, R, P, N]

def bishopCompactnessCriterionToEventFlow :
    BishopCompactnessCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCompactnessCriterionFields x).map bishopCompactnessCriterionEncodeBHist

private def bishopCompactnessCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompactnessCriterionEventAtDefault index rest

def bishopCompactnessCriterionFromEventFlow :
    EventFlow → Option BishopCompactnessCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopCompactnessCriterionUp.mk
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 0 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 1 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 2 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 3 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 4 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 5 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 6 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 7 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 8 ef))
          (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEventAtDefault 9 ef)))

private theorem BishopCompactnessCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCompactnessCriterionUp,
      bishopCompactnessCriterionFromEventFlow (bishopCompactnessCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T F C L Q H R P N =>
      change
        some
          (BishopCompactnessCriterionUp.mk
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist M))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist T))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist F))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist C))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist L))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist Q))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist H))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist R))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist P))
            (bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist N))) =
          some (BishopCompactnessCriterionUp.mk M T F C L Q H R P N)
      rw [BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode M,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode T,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode F,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode C,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode L,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode Q,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode H,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode R,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode P,
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode N]

private theorem BishopCompactnessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompactnessCriterionUp} :
    bishopCompactnessCriterionToEventFlow x = bishopCompactnessCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompactnessCriterionFromEventFlow (bishopCompactnessCriterionToEventFlow x) =
        bishopCompactnessCriterionFromEventFlow (bishopCompactnessCriterionToEventFlow y) :=
    congrArg bishopCompactnessCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCompactnessCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCompactnessCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCompactnessCriterionTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopCompactnessCriterionUp,
      bishopCompactnessCriterionFields x = bishopCompactnessCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 T1 F1 C1 L1 Q1 H1 R1 P1 N1 =>
      cases y with
      | mk M2 T2 F2 C2 L2 Q2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance bishopCompactnessCriterionBHistCarrier :
    BHistCarrier BishopCompactnessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompactnessCriterionToEventFlow
  fromEventFlow := bishopCompactnessCriterionFromEventFlow

instance bishopCompactnessCriterionChapterTasteGate :
    ChapterTasteGate BishopCompactnessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompactnessCriterionFromEventFlow (bishopCompactnessCriterionToEventFlow x) =
      some x
    exact BishopCompactnessCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCompactnessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopCompactnessCriterionFieldFaithful :
    FieldFaithful BishopCompactnessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompactnessCriterionFields
  field_faithful := BishopCompactnessCriterionTasteGate_single_carrier_alignment_fields

instance bishopCompactnessCriterionNontrivial :
    Nontrivial BishopCompactnessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompactnessCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCompactnessCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopCompactnessCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompactnessCriterionChapterTasteGate

theorem BishopCompactnessCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCompactnessCriterionDecodeBHist (bishopCompactnessCriterionEncodeBHist h) = h) ∧
      (∀ x : BishopCompactnessCriterionUp,
        bishopCompactnessCriterionFromEventFlow (bishopCompactnessCriterionToEventFlow x) =
          some x) ∧
        (∀ x y : BishopCompactnessCriterionUp,
          bishopCompactnessCriterionToEventFlow x = bishopCompactnessCriterionToEventFlow y →
            x = y) ∧
          bishopCompactnessCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BishopCompactnessCriterionTasteGate_single_carrier_alignment_decode,
      BishopCompactnessCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopCompactnessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopCompactnessCriterionUp
