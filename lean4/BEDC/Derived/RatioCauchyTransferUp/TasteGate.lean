import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RatioCauchyTransferUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RatioCauchyTransferUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (N D A R Q H C P L : BHist) : RatioCauchyTransferUp
  deriving DecidableEq

def ratioCauchyTransferEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ratioCauchyTransferEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ratioCauchyTransferEncodeBHist h

def ratioCauchyTransferDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ratioCauchyTransferDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ratioCauchyTransferDecodeBHist tail)

private theorem RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ratioCauchyTransferFields : RatioCauchyTransferUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RatioCauchyTransferUp.mk N D A R Q H C P L => [N, D, A, R, Q, H, C, P, L]

def ratioCauchyTransferToEventFlow : RatioCauchyTransferUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ratioCauchyTransferFields x).map ratioCauchyTransferEncodeBHist

private def ratioCauchyTransferEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ratioCauchyTransferEventAt index rest

def ratioCauchyTransferFromEventFlow (ef : EventFlow) : Option RatioCauchyTransferUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RatioCauchyTransferUp.mk
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 0 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 1 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 2 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 3 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 4 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 5 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 6 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 7 ef))
      (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEventAt 8 ef)))

private theorem RatioCauchyTransferTasteGate_single_carrier_alignment_round_trip
    (x : RatioCauchyTransferUp) :
    ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk N D A R Q H C P L =>
      change
        some
          (RatioCauchyTransferUp.mk
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist N))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist D))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist A))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist R))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist Q))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist H))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist C))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist P))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist L))) =
          some (RatioCauchyTransferUp.mk N D A R Q H C P L)
      rw [RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode N,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode D,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode A,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode R,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode Q,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode H,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode C,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode P,
        RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode L]

private theorem RatioCauchyTransferTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RatioCauchyTransferUp} :
    ratioCauchyTransferToEventFlow x = ratioCauchyTransferToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) =
        ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow y) :=
    congrArg ratioCauchyTransferFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RatioCauchyTransferTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RatioCauchyTransferTasteGate_single_carrier_alignment_round_trip y)))

private theorem RatioCauchyTransferTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RatioCauchyTransferUp,
      ratioCauchyTransferFields x = ratioCauchyTransferFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk N₁ D₁ A₁ R₁ Q₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk N₂ D₂ A₂ R₂ Q₂ H₂ C₂ P₂ L₂ =>
          cases hfields
          rfl

instance ratioCauchyTransferBHistCarrier : BHistCarrier RatioCauchyTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ratioCauchyTransferToEventFlow
  fromEventFlow := ratioCauchyTransferFromEventFlow

instance ratioCauchyTransferChapterTasteGate :
    ChapterTasteGate RatioCauchyTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) = some x
    exact RatioCauchyTransferTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RatioCauchyTransferTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ratioCauchyTransferFieldFaithful : FieldFaithful RatioCauchyTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ratioCauchyTransferFields
  field_faithful := RatioCauchyTransferTasteGate_single_carrier_alignment_fields_faithful

instance ratioCauchyTransferNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RatioCauchyTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RatioCauchyTransferUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RatioCauchyTransferUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RatioCauchyTransferUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ratioCauchyTransferChapterTasteGate

theorem RatioCauchyTransferTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RatioCauchyTransferUp) ∧
      Nonempty (FieldFaithful RatioCauchyTransferUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RatioCauchyTransferUp) ∧
          (∀ h : BHist,
            ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist h) = h) ∧
            (∀ x : RatioCauchyTransferUp,
              ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) = some x) ∧
              (∀ x y : RatioCauchyTransferUp,
                ratioCauchyTransferToEventFlow x = ratioCauchyTransferToEventFlow y → x = y) ∧
                ratioCauchyTransferEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨ratioCauchyTransferChapterTasteGate⟩,
      ⟨ratioCauchyTransferFieldFaithful⟩,
      ⟨ratioCauchyTransferNontrivial⟩,
      RatioCauchyTransferTasteGate_single_carrier_alignment_decode_encode,
      RatioCauchyTransferTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RatioCauchyTransferTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RatioCauchyTransferUp.TasteGate
