import BEDC.Derived.RiemannRearrangementUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannRearrangementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def riemannRearrangementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannRearrangementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannRearrangementEncodeBHist h

def riemannRearrangementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannRearrangementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannRearrangementDecodeBHist tail)

private theorem RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def riemannRearrangementFields : RiemannRearrangementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannRearrangementUp.mk S Q P M Pi B G E H C K N => [S, Q, P, M, Pi, B, G, E, H, C, K, N]

def riemannRearrangementToEventFlow : RiemannRearrangementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannRearrangementFields x).map riemannRearrangementEncodeBHist

private def riemannRearrangementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannRearrangementEventAtDefault index rest

def riemannRearrangementFromEventFlow (ef : EventFlow) : Option RiemannRearrangementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (RiemannRearrangementUp.mk
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 0 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 1 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 2 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 3 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 4 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 5 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 6 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 7 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 8 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 9 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 10 ef))
      (riemannRearrangementDecodeBHist (riemannRearrangementEventAtDefault 11 ef)))

private theorem RiemannRearrangementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannRearrangementUp, riemannRearrangementFromEventFlow (riemannRearrangementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q P M Pi B G E H C K N =>
      change
        some (RiemannRearrangementUp.mk
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist S))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist Q))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist P))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist M))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist Pi))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist B))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist G))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist E))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist H))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist C))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist K))
          (riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist N))
          ) = some (RiemannRearrangementUp.mk S Q P M Pi B G E H C K N)
      rw [RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode S, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode Q, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode P, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode M, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode Pi, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode B, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode G, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode E, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode H, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode C, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode K, RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannRearrangementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannRearrangementUp} :
    riemannRearrangementToEventFlow x = riemannRearrangementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannRearrangementFromEventFlow (riemannRearrangementToEventFlow x) =
        riemannRearrangementFromEventFlow (riemannRearrangementToEventFlow y) :=
    congrArg riemannRearrangementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannRearrangementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RiemannRearrangementTasteGate_single_carrier_alignment_round_trip y)))

private theorem RiemannRearrangementTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RiemannRearrangementUp, riemannRearrangementFields x = riemannRearrangementFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Q₁ P₁ M₁ Pi₁ B₁ G₁ E₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk S₂ Q₂ P₂ M₂ Pi₂ B₂ G₂ E₂ H₂ C₂ K₂ N₂ =>
          cases hfields
          rfl

instance riemannRearrangementBHistCarrier : BHistCarrier RiemannRearrangementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannRearrangementToEventFlow
  fromEventFlow := riemannRearrangementFromEventFlow

instance riemannRearrangementChapterTasteGate : ChapterTasteGate RiemannRearrangementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannRearrangementFromEventFlow (riemannRearrangementToEventFlow x) = some x
    exact RiemannRearrangementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannRearrangementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance riemannRearrangementFieldFaithful : FieldFaithful RiemannRearrangementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannRearrangementFields
  field_faithful := RiemannRearrangementTasteGate_single_carrier_alignment_fields_faithful

instance riemannRearrangementNontrivial : Nontrivial RiemannRearrangementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannRearrangementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RiemannRearrangementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RiemannRearrangementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannRearrangementChapterTasteGate

theorem RiemannRearrangementTasteGate_single_carrier_alignment :
    (∀ h : BHist, riemannRearrangementDecodeBHist (riemannRearrangementEncodeBHist h) = h) ∧
      (∀ x : RiemannRearrangementUp, riemannRearrangementFromEventFlow (riemannRearrangementToEventFlow x) = some x) ∧
        (∀ x y : RiemannRearrangementUp,
          riemannRearrangementToEventFlow x = riemannRearrangementToEventFlow y → x = y) ∧
          riemannRearrangementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RiemannRearrangementTasteGate_single_carrier_alignment_decode_encode,
      RiemannRearrangementTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RiemannRearrangementTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RiemannRearrangementUp
