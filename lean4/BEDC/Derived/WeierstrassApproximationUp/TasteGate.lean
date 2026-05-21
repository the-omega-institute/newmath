import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeierstrassApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeierstrassApproximationUp : Type where
  | mk (I F epsilon P S M E T C R Q : BHist) : WeierstrassApproximationUp
  deriving DecidableEq

def weierstrassApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weierstrassApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weierstrassApproximationEncodeBHist h

def weierstrassApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weierstrassApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weierstrassApproximationDecodeBHist tail)

private theorem weierstrassApproximation_decode_encode_bhist :
    ∀ h : BHist,
      weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weierstrassApproximationFields : WeierstrassApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeierstrassApproximationUp.mk I F epsilon P S M E T C R Q =>
      [I, F, epsilon, P, S, M, E, T, C, R, Q]

def weierstrassApproximationToEventFlow : WeierstrassApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (weierstrassApproximationFields x).map weierstrassApproximationEncodeBHist

private def weierstrassApproximationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => weierstrassApproximationEventAt index rest

def weierstrassApproximationFromEventFlow : EventFlow → Option WeierstrassApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (WeierstrassApproximationUp.mk
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 0 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 1 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 2 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 3 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 4 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 5 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 6 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 7 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 8 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 9 ef))
          (weierstrassApproximationDecodeBHist (weierstrassApproximationEventAt 10 ef)))

private theorem weierstrassApproximation_round_trip :
    ∀ x : WeierstrassApproximationUp,
      weierstrassApproximationFromEventFlow (weierstrassApproximationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F epsilon P S M E T C R Q =>
      change
        some
          (WeierstrassApproximationUp.mk
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist I))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist F))
            (weierstrassApproximationDecodeBHist
              (weierstrassApproximationEncodeBHist epsilon))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist P))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist S))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist M))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist E))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist T))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist C))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist R))
            (weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist Q))) =
          some (WeierstrassApproximationUp.mk I F epsilon P S M E T C R Q)
      rw [weierstrassApproximation_decode_encode_bhist I,
        weierstrassApproximation_decode_encode_bhist F,
        weierstrassApproximation_decode_encode_bhist epsilon,
        weierstrassApproximation_decode_encode_bhist P,
        weierstrassApproximation_decode_encode_bhist S,
        weierstrassApproximation_decode_encode_bhist M,
        weierstrassApproximation_decode_encode_bhist E,
        weierstrassApproximation_decode_encode_bhist T,
        weierstrassApproximation_decode_encode_bhist C,
        weierstrassApproximation_decode_encode_bhist R,
        weierstrassApproximation_decode_encode_bhist Q]

private theorem weierstrassApproximationToEventFlow_injective
    {x y : WeierstrassApproximationUp} :
    weierstrassApproximationToEventFlow x = weierstrassApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weierstrassApproximationFromEventFlow (weierstrassApproximationToEventFlow x) =
        weierstrassApproximationFromEventFlow (weierstrassApproximationToEventFlow y) :=
    congrArg weierstrassApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (weierstrassApproximation_round_trip x).symm
      (Eq.trans hread (weierstrassApproximation_round_trip y)))

private theorem weierstrassApproximation_field_faithful :
    ∀ x y : WeierstrassApproximationUp,
      weierstrassApproximationFields x = weierstrassApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ epsilon₁ P₁ S₁ M₁ E₁ T₁ C₁ R₁ Q₁ =>
      cases y with
      | mk I₂ F₂ epsilon₂ P₂ S₂ M₂ E₂ T₂ C₂ R₂ Q₂ =>
          cases hfields
          rfl

instance weierstrassApproximationBHistCarrier : BHistCarrier WeierstrassApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weierstrassApproximationToEventFlow
  fromEventFlow := weierstrassApproximationFromEventFlow

instance weierstrassApproximationChapterTasteGate :
    ChapterTasteGate WeierstrassApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      weierstrassApproximationFromEventFlow (weierstrassApproximationToEventFlow x) =
        some x
    exact weierstrassApproximation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (weierstrassApproximationToEventFlow_injective heq)

instance weierstrassApproximationFieldFaithful : FieldFaithful WeierstrassApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := weierstrassApproximationFields
  field_faithful := weierstrassApproximation_field_faithful

def taste_gate : ChapterTasteGate WeierstrassApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weierstrassApproximationChapterTasteGate

theorem WeierstrassApproximationTasteGate_single_carrier_alignment :
    (weierstrassApproximationEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (∀ h : BHist,
        weierstrassApproximationDecodeBHist (weierstrassApproximationEncodeBHist h) = h) ∧
        (∀ x : WeierstrassApproximationUp,
          weierstrassApproximationFromEventFlow (weierstrassApproximationToEventFlow x) =
            some x) ∧
          (∀ x y : WeierstrassApproximationUp,
            weierstrassApproximationFields x = weierstrassApproximationFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact weierstrassApproximation_decode_encode_bhist
    · constructor
      · exact weierstrassApproximation_round_trip
      · exact weierstrassApproximation_field_faithful

end BEDC.Derived.WeierstrassApproximationUp
