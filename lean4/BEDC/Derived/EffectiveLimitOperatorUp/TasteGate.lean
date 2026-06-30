import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveLimitOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveLimitOperatorUp : Type where
  | mk (X A S M R D E H C P N : BHist) : EffectiveLimitOperatorUp
  deriving DecidableEq

def effectiveLimitOperatorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveLimitOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveLimitOperatorEncodeBHist h

def effectiveLimitOperatorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveLimitOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveLimitOperatorDecodeBHist tail)

private theorem EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveLimitOperatorFields : EffectiveLimitOperatorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveLimitOperatorUp.mk X A S M R D E H C P N => [X, A, S, M, R, D, E, H, C, P, N]

def effectiveLimitOperatorToEventFlow : EffectiveLimitOperatorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (effectiveLimitOperatorFields x).map effectiveLimitOperatorEncodeBHist

def effectiveLimitOperatorEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveLimitOperatorEventAt index rest

def effectiveLimitOperatorFromEventFlow : EventFlow -> Option EffectiveLimitOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (EffectiveLimitOperatorUp.mk
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 0 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 1 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 2 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 3 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 4 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 5 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 6 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 7 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 8 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 9 flow))
          (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEventAt 10 flow)))

private theorem EffectiveLimitOperatorTasteGate_single_carrier_alignment_round_trip :
    forall x : EffectiveLimitOperatorUp,
      effectiveLimitOperatorFromEventFlow (effectiveLimitOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A S M R D E H C P N =>
      change
        some
          (EffectiveLimitOperatorUp.mk
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist X))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist A))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist S))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist M))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist R))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist D))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist E))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist H))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist C))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist P))
            (effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist N))) =
          some (EffectiveLimitOperatorUp.mk X A S M R D E H C P N)
      rw [EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode X,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode A,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode S,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode M,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode R,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode D,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode E,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode H,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode C,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode P,
        EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode N]

private theorem effectiveLimitOperatorToEventFlow_injective {x y : EffectiveLimitOperatorUp} :
    effectiveLimitOperatorToEventFlow x = effectiveLimitOperatorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveLimitOperatorFromEventFlow (effectiveLimitOperatorToEventFlow x) =
        effectiveLimitOperatorFromEventFlow (effectiveLimitOperatorToEventFlow y) :=
    congrArg effectiveLimitOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EffectiveLimitOperatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EffectiveLimitOperatorTasteGate_single_carrier_alignment_round_trip y)))

private theorem EffectiveLimitOperatorTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : EffectiveLimitOperatorUp,
      effectiveLimitOperatorFields x = effectiveLimitOperatorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 A1 S1 M1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 S2 M2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance effectiveLimitOperatorBHistCarrier : BHistCarrier EffectiveLimitOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveLimitOperatorToEventFlow
  fromEventFlow := effectiveLimitOperatorFromEventFlow

instance effectiveLimitOperatorChapterTasteGate : ChapterTasteGate EffectiveLimitOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveLimitOperatorFromEventFlow (effectiveLimitOperatorToEventFlow x) = some x
    exact EffectiveLimitOperatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveLimitOperatorToEventFlow_injective heq)

instance effectiveLimitOperatorFieldFaithful : FieldFaithful EffectiveLimitOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectiveLimitOperatorFields
  field_faithful := EffectiveLimitOperatorTasteGate_single_carrier_alignment_fields_faithful

instance effectiveLimitOperatorNontrivial : Nontrivial EffectiveLimitOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EffectiveLimitOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EffectiveLimitOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EffectiveLimitOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveLimitOperatorChapterTasteGate

theorem EffectiveLimitOperatorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EffectiveLimitOperatorUp) ∧
      Nonempty (FieldFaithful EffectiveLimitOperatorUp) ∧
      Nonempty (Nontrivial EffectiveLimitOperatorUp) ∧
      (∀ h : BHist,
        effectiveLimitOperatorDecodeBHist (effectiveLimitOperatorEncodeBHist h) = h) ∧
      (∀ x : EffectiveLimitOperatorUp,
        effectiveLimitOperatorFromEventFlow (effectiveLimitOperatorToEventFlow x) = some x) ∧
      (∀ x y : EffectiveLimitOperatorUp,
        effectiveLimitOperatorToEventFlow x = effectiveLimitOperatorToEventFlow y -> x = y) ∧
      effectiveLimitOperatorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨effectiveLimitOperatorChapterTasteGate⟩,
      ⟨⟨effectiveLimitOperatorFieldFaithful⟩,
        ⟨⟨effectiveLimitOperatorNontrivial⟩,
          ⟨EffectiveLimitOperatorTasteGate_single_carrier_alignment_decode,
            ⟨EffectiveLimitOperatorTasteGate_single_carrier_alignment_round_trip,
              ⟨fun _ _ heq => effectiveLimitOperatorToEventFlow_injective heq, rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.EffectiveLimitOperatorUp
