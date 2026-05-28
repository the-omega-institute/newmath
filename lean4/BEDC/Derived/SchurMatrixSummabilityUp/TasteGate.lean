import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchurMatrixSummabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchurMatrixSummabilityUp : Type where
  | mk (M B C W T R E H Q P N : BHist) : SchurMatrixSummabilityUp
  deriving DecidableEq

def schurMatrixSummabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schurMatrixSummabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schurMatrixSummabilityEncodeBHist h

def schurMatrixSummabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schurMatrixSummabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schurMatrixSummabilityDecodeBHist tail)

private theorem SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schurMatrixSummabilityFields : SchurMatrixSummabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchurMatrixSummabilityUp.mk M B C W T R E H Q P N => [M, B, C, W, T, R, E, H, Q, P, N]

def schurMatrixSummabilityToEventFlow : SchurMatrixSummabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (schurMatrixSummabilityFields x).map schurMatrixSummabilityEncodeBHist

private def schurMatrixSummabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schurMatrixSummabilityEventAtDefault index rest

def schurMatrixSummabilityFromEventFlow :
    EventFlow → Option SchurMatrixSummabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SchurMatrixSummabilityUp.mk
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 0 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 1 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 2 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 3 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 4 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 5 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 6 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 7 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 8 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 9 ef))
          (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEventAtDefault 10 ef)))

private theorem SchurMatrixSummabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SchurMatrixSummabilityUp,
      schurMatrixSummabilityFromEventFlow (schurMatrixSummabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B C W T R E H Q P N =>
      change
        some
          (SchurMatrixSummabilityUp.mk
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist M))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist B))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist C))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist W))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist T))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist R))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist E))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist H))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist Q))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist P))
            (schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist N))) =
          some (SchurMatrixSummabilityUp.mk M B C W T R E H Q P N)
      rw [SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode M,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode B,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode C,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode W,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode T,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode R,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode E,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode H,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode Q,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode P,
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode N]

private theorem SchurMatrixSummabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SchurMatrixSummabilityUp} :
    schurMatrixSummabilityToEventFlow x = schurMatrixSummabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schurMatrixSummabilityFromEventFlow (schurMatrixSummabilityToEventFlow x) =
        schurMatrixSummabilityFromEventFlow (schurMatrixSummabilityToEventFlow y) :=
    congrArg schurMatrixSummabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SchurMatrixSummabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SchurMatrixSummabilityTasteGate_single_carrier_alignment_round_trip y)))

private theorem SchurMatrixSummabilityTasteGate_single_carrier_alignment_fields :
    ∀ x y : SchurMatrixSummabilityUp,
      schurMatrixSummabilityFields x = schurMatrixSummabilityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 B1 C1 W1 T1 R1 E1 H1 Q1 P1 N1 =>
      cases y with
      | mk M2 B2 C2 W2 T2 R2 E2 H2 Q2 P2 N2 =>
          cases hfields
          rfl

instance schurMatrixSummabilityBHistCarrier :
    BHistCarrier SchurMatrixSummabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schurMatrixSummabilityToEventFlow
  fromEventFlow := schurMatrixSummabilityFromEventFlow

instance schurMatrixSummabilityChapterTasteGate :
    ChapterTasteGate SchurMatrixSummabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schurMatrixSummabilityFromEventFlow (schurMatrixSummabilityToEventFlow x) =
      some x
    exact SchurMatrixSummabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SchurMatrixSummabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance schurMatrixSummabilityFieldFaithful :
    FieldFaithful SchurMatrixSummabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := schurMatrixSummabilityFields
  field_faithful := SchurMatrixSummabilityTasteGate_single_carrier_alignment_fields

instance schurMatrixSummabilityNontrivial :
    Nontrivial SchurMatrixSummabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SchurMatrixSummabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SchurMatrixSummabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SchurMatrixSummabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schurMatrixSummabilityChapterTasteGate

theorem SchurMatrixSummabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      schurMatrixSummabilityDecodeBHist (schurMatrixSummabilityEncodeBHist h) = h) ∧
      (∀ x : SchurMatrixSummabilityUp,
        schurMatrixSummabilityFromEventFlow (schurMatrixSummabilityToEventFlow x) =
          some x) ∧
        (∀ x y : SchurMatrixSummabilityUp,
          schurMatrixSummabilityToEventFlow x = schurMatrixSummabilityToEventFlow y →
            x = y) ∧
          schurMatrixSummabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SchurMatrixSummabilityTasteGate_single_carrier_alignment_decode,
      SchurMatrixSummabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SchurMatrixSummabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SchurMatrixSummabilityUp
