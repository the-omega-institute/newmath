import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CoxeterGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CoxeterGroupUp : Type where
  | mk (S M W R N H Q P L : BHist) : CoxeterGroupUp
  deriving DecidableEq

def coxeterGroupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: coxeterGroupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: coxeterGroupEncodeBHist h

def coxeterGroupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (coxeterGroupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (coxeterGroupDecodeBHist tail)

private theorem CoxeterGroupTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, coxeterGroupDecodeBHist (coxeterGroupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def coxeterGroupFields : CoxeterGroupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CoxeterGroupUp.mk S M W R N H Q P L => [S, M, W, R, N, H, Q, P, L]

def coxeterGroupToEventFlow : CoxeterGroupUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (coxeterGroupFields x).map coxeterGroupEncodeBHist

private def coxeterGroupEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => coxeterGroupEventAt index rest

def coxeterGroupFromEventFlow (ef : EventFlow) : Option CoxeterGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CoxeterGroupUp.mk
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 0 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 1 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 2 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 3 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 4 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 5 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 6 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 7 ef))
      (coxeterGroupDecodeBHist (coxeterGroupEventAt 8 ef)))

private theorem CoxeterGroupTasteGate_single_carrier_alignment_round_trip
    (x : CoxeterGroupUp) :
    coxeterGroupFromEventFlow (coxeterGroupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M W R N H Q P L =>
      change
        some
          (CoxeterGroupUp.mk
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist S))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist M))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist W))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist R))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist N))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist H))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist Q))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist P))
            (coxeterGroupDecodeBHist (coxeterGroupEncodeBHist L))) =
          some (CoxeterGroupUp.mk S M W R N H Q P L)
      rw [CoxeterGroupTasteGate_single_carrier_alignment_decode_encode S,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode M,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode W,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode R,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode N,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode H,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode Q,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode P,
        CoxeterGroupTasteGate_single_carrier_alignment_decode_encode L]

private theorem CoxeterGroupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CoxeterGroupUp} :
    coxeterGroupToEventFlow x = coxeterGroupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      coxeterGroupFromEventFlow (coxeterGroupToEventFlow x) =
        coxeterGroupFromEventFlow (coxeterGroupToEventFlow y) :=
    congrArg coxeterGroupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CoxeterGroupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CoxeterGroupTasteGate_single_carrier_alignment_round_trip y)))

private theorem CoxeterGroupTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CoxeterGroupUp, coxeterGroupFields x = coxeterGroupFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ W₁ R₁ N₁ H₁ Q₁ P₁ L₁ =>
      cases y with
      | mk S₂ M₂ W₂ R₂ N₂ H₂ Q₂ P₂ L₂ =>
          cases hfields
          rfl

instance coxeterGroupBHistCarrier : BHistCarrier CoxeterGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := coxeterGroupToEventFlow
  fromEventFlow := coxeterGroupFromEventFlow

instance coxeterGroupChapterTasteGate : ChapterTasteGate CoxeterGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change coxeterGroupFromEventFlow (coxeterGroupToEventFlow x) = some x
    exact CoxeterGroupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CoxeterGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance coxeterGroupFieldFaithful : FieldFaithful CoxeterGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := coxeterGroupFields
  field_faithful := CoxeterGroupTasteGate_single_carrier_alignment_fields_faithful

instance coxeterGroupNontrivial : Nontrivial CoxeterGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CoxeterGroupUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CoxeterGroupUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CoxeterGroupTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CoxeterGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  coxeterGroupChapterTasteGate

theorem CoxeterGroupTasteGate_single_carrier_alignment :
    (∀ h : BHist, coxeterGroupDecodeBHist (coxeterGroupEncodeBHist h) = h) ∧
      (∀ x : CoxeterGroupUp,
        coxeterGroupFromEventFlow (coxeterGroupToEventFlow x) = some x) ∧
        (∀ x y : CoxeterGroupUp,
          coxeterGroupToEventFlow x = coxeterGroupToEventFlow y → x = y) ∧
          coxeterGroupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CoxeterGroupTasteGate_single_carrier_alignment_decode_encode,
      CoxeterGroupTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CoxeterGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CoxeterGroupUp
