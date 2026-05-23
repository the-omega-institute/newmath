import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalBallUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalBallUp : Type where
  | mk :
      (center radius orderWitness transportLedger containmentLedger provenance localNameCert :
        BHist) →
        RationalBallUp
  deriving DecidableEq

def rationalBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalBallEncodeBHist h

def rationalBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalBallDecodeBHist tail)

private theorem RationalBallTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, rationalBallDecodeBHist (rationalBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalBallFields : RationalBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalBallUp.mk center radius orderWitness transportLedger containmentLedger provenance
      localNameCert =>
      [center, radius, orderWitness, transportLedger, containmentLedger, provenance,
        localNameCert]

def rationalBallToEventFlow : RationalBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalBallFields x).map rationalBallEncodeBHist

private def rationalBallEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalBallEventAt index rest

def rationalBallFromEventFlow (ef : EventFlow) : Option RationalBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalBallUp.mk
      (rationalBallDecodeBHist (rationalBallEventAt 0 ef))
      (rationalBallDecodeBHist (rationalBallEventAt 1 ef))
      (rationalBallDecodeBHist (rationalBallEventAt 2 ef))
      (rationalBallDecodeBHist (rationalBallEventAt 3 ef))
      (rationalBallDecodeBHist (rationalBallEventAt 4 ef))
      (rationalBallDecodeBHist (rationalBallEventAt 5 ef))
      (rationalBallDecodeBHist (rationalBallEventAt 6 ef)))

private theorem RationalBallTasteGate_single_carrier_alignment_round_trip
    (x : RationalBallUp) :
    rationalBallFromEventFlow (rationalBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk center radius orderWitness transportLedger containmentLedger provenance localNameCert =>
      change
        some
          (RationalBallUp.mk
            (rationalBallDecodeBHist (rationalBallEncodeBHist center))
            (rationalBallDecodeBHist (rationalBallEncodeBHist radius))
            (rationalBallDecodeBHist (rationalBallEncodeBHist orderWitness))
            (rationalBallDecodeBHist (rationalBallEncodeBHist transportLedger))
            (rationalBallDecodeBHist (rationalBallEncodeBHist containmentLedger))
            (rationalBallDecodeBHist (rationalBallEncodeBHist provenance))
            (rationalBallDecodeBHist (rationalBallEncodeBHist localNameCert))) =
          some
            (RationalBallUp.mk center radius orderWitness transportLedger containmentLedger
              provenance localNameCert)
      rw [RationalBallTasteGate_single_carrier_alignment_decode_encode center,
        RationalBallTasteGate_single_carrier_alignment_decode_encode radius,
        RationalBallTasteGate_single_carrier_alignment_decode_encode orderWitness,
        RationalBallTasteGate_single_carrier_alignment_decode_encode transportLedger,
        RationalBallTasteGate_single_carrier_alignment_decode_encode containmentLedger,
        RationalBallTasteGate_single_carrier_alignment_decode_encode provenance,
        RationalBallTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem RationalBallTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalBallUp} :
    rationalBallToEventFlow x = rationalBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalBallFromEventFlow (rationalBallToEventFlow x) =
        rationalBallFromEventFlow (rationalBallToEventFlow y) :=
    congrArg rationalBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalBallTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RationalBallTasteGate_single_carrier_alignment_round_trip y)))

private theorem RationalBallTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RationalBallUp, rationalBallFields x = rationalBallFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk center₁ radius₁ orderWitness₁ transportLedger₁ containmentLedger₁ provenance₁
      localNameCert₁ =>
      cases y with
      | mk center₂ radius₂ orderWitness₂ transportLedger₂ containmentLedger₂ provenance₂
          localNameCert₂ =>
          cases hfields
          rfl

instance rationalBallBHistCarrier : BHistCarrier RationalBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalBallToEventFlow
  fromEventFlow := rationalBallFromEventFlow

instance rationalBallChapterTasteGate : ChapterTasteGate RationalBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalBallFromEventFlow (rationalBallToEventFlow x) = some x
    exact RationalBallTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalBallTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rationalBallFieldFaithful : FieldFaithful RationalBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalBallFields
  field_faithful := RationalBallTasteGate_single_carrier_alignment_fields_faithful

instance rationalBallNontrivial : Nontrivial RationalBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RationalBallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RationalBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RationalBallTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RationalBallUp) ∧ Nonempty (FieldFaithful RationalBallUp) ∧
      Nonempty (Nontrivial RationalBallUp) ∧
        (∀ h : BHist, rationalBallDecodeBHist (rationalBallEncodeBHist h) = h) ∧
          (∀ x : RationalBallUp, rationalBallFromEventFlow (rationalBallToEventFlow x) =
            some x) ∧
            (∀ x y : RationalBallUp,
              rationalBallToEventFlow x = rationalBallToEventFlow y → x = y) ∧
              rationalBallEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨rationalBallChapterTasteGate⟩
  · constructor
    · exact ⟨rationalBallFieldFaithful⟩
    · constructor
      · exact ⟨rationalBallNontrivial⟩
      · constructor
        · exact RationalBallTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · intro x
            exact RationalBallTasteGate_single_carrier_alignment_round_trip x
          · constructor
            · intro x y heq
              exact RationalBallTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.RationalBallUp.TasteGate
