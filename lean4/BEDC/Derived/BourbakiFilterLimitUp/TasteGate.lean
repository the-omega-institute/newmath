import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BourbakiFilterLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BourbakiFilterLimitUp : Type where
  | mk (basis cauchy convergence window readback dyadic realSeal transport replay
      provenance localName : BHist) : BourbakiFilterLimitUp
  deriving DecidableEq

def bourbakiFilterLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bourbakiFilterLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bourbakiFilterLimitEncodeBHist h

def bourbakiFilterLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bourbakiFilterLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bourbakiFilterLimitDecodeBHist tail)

private theorem BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bourbakiFilterLimitFields : BourbakiFilterLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BourbakiFilterLimitUp.mk basis cauchy convergence window readback dyadic realSeal
      transport replay provenance localName =>
      [basis, cauchy, convergence, window, readback, dyadic, realSeal, transport, replay,
        provenance, localName]

def bourbakiFilterLimitToEventFlow : BourbakiFilterLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bourbakiFilterLimitFields x).map bourbakiFilterLimitEncodeBHist

private def bourbakiFilterLimitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bourbakiFilterLimitEventAt index rest

def bourbakiFilterLimitFromEventFlow (ef : EventFlow) : Option BourbakiFilterLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BourbakiFilterLimitUp.mk
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 0 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 1 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 2 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 3 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 4 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 5 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 6 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 7 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 8 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 9 ef))
      (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEventAt 10 ef)))

private theorem BourbakiFilterLimitTasteGate_single_carrier_alignment_round_trip
    (x : BourbakiFilterLimitUp) :
    bourbakiFilterLimitFromEventFlow (bourbakiFilterLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk basis cauchy convergence window readback dyadic realSeal transport replay provenance
      localName =>
      change
        some
          (BourbakiFilterLimitUp.mk
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist basis))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist cauchy))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist convergence))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist window))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist readback))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist dyadic))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist realSeal))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist transport))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist replay))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist provenance))
            (bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist localName))) =
          some
            (BourbakiFilterLimitUp.mk basis cauchy convergence window readback dyadic
              realSeal transport replay provenance localName)
      rw [BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode basis,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode cauchy,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode convergence,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode window,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode readback,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode dyadic,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode realSeal,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode transport,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode replay,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode provenance,
        BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode localName]

private theorem BourbakiFilterLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BourbakiFilterLimitUp} :
    bourbakiFilterLimitToEventFlow x = bourbakiFilterLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bourbakiFilterLimitFromEventFlow (bourbakiFilterLimitToEventFlow x) =
        bourbakiFilterLimitFromEventFlow (bourbakiFilterLimitToEventFlow y) :=
    congrArg bourbakiFilterLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BourbakiFilterLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BourbakiFilterLimitTasteGate_single_carrier_alignment_round_trip y)))

private theorem BourbakiFilterLimitTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BourbakiFilterLimitUp, bourbakiFilterLimitFields x = bourbakiFilterLimitFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk basis₁ cauchy₁ convergence₁ window₁ readback₁ dyadic₁ realSeal₁ transport₁
      replay₁ provenance₁ localName₁ =>
      cases y with
      | mk basis₂ cauchy₂ convergence₂ window₂ readback₂ dyadic₂ realSeal₂ transport₂
          replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance bourbakiFilterLimitBHistCarrier : BHistCarrier BourbakiFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bourbakiFilterLimitToEventFlow
  fromEventFlow := bourbakiFilterLimitFromEventFlow

instance bourbakiFilterLimitChapterTasteGate :
    ChapterTasteGate BourbakiFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bourbakiFilterLimitFromEventFlow (bourbakiFilterLimitToEventFlow x) = some x
    exact BourbakiFilterLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BourbakiFilterLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bourbakiFilterLimitFieldFaithful : FieldFaithful BourbakiFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bourbakiFilterLimitFields
  field_faithful := BourbakiFilterLimitTasteGate_single_carrier_alignment_fields_faithful

instance bourbakiFilterLimitNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BourbakiFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BourbakiFilterLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BourbakiFilterLimitUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def bourbakiFilterLimitTasteGate : ChapterTasteGate BourbakiFilterLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bourbakiFilterLimitChapterTasteGate

theorem BourbakiFilterLimitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BourbakiFilterLimitUp) ∧
      Nonempty (FieldFaithful BourbakiFilterLimitUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BourbakiFilterLimitUp) ∧
          (∀ h : BHist, bourbakiFilterLimitDecodeBHist (bourbakiFilterLimitEncodeBHist h) = h) ∧
            (∀ x : BourbakiFilterLimitUp,
              bourbakiFilterLimitFromEventFlow (bourbakiFilterLimitToEventFlow x) = some x) ∧
              bourbakiFilterLimitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨bourbakiFilterLimitChapterTasteGate⟩,
      ⟨⟨bourbakiFilterLimitFieldFaithful⟩,
        ⟨⟨bourbakiFilterLimitNontrivial⟩,
          BourbakiFilterLimitTasteGate_single_carrier_alignment_decode_encode,
          BourbakiFilterLimitTasteGate_single_carrier_alignment_round_trip,
          rfl⟩⟩⟩

end BEDC.Derived.BourbakiFilterLimitUp
