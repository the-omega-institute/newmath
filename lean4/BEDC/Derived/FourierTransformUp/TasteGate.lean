import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FourierTransformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FourierTransformUp : Type where
  | mk (W K I R V H C P N : BHist) : FourierTransformUp
  deriving DecidableEq

def fourierTransformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fourierTransformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fourierTransformEncodeBHist h

def fourierTransformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fourierTransformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fourierTransformDecodeBHist tail)

private theorem fourierTransform_decode_encode_bhist :
    ∀ h : BHist, fourierTransformDecodeBHist (fourierTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fourierTransformFields : FourierTransformUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FourierTransformUp.mk W K I R V H C P N => [W, K, I, R, V, H, C, P, N]

def fourierTransformToEventFlow : FourierTransformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fourierTransformFields x).map fourierTransformEncodeBHist

private def fourierTransformEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fourierTransformEventAtDefault index rest

def fourierTransformFromEventFlow (ef : EventFlow) : Option FourierTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FourierTransformUp.mk
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 0 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 1 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 2 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 3 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 4 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 5 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 6 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 7 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 8 ef)))

private theorem fourierTransform_round_trip :
    ∀ x : FourierTransformUp,
      fourierTransformFromEventFlow (fourierTransformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W K I R V H C P N =>
      change
        some
          (FourierTransformUp.mk
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist W))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist K))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist I))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) =
          some (FourierTransformUp.mk W K I R V H C P N)
      rw [fourierTransform_decode_encode_bhist W, fourierTransform_decode_encode_bhist K,
        fourierTransform_decode_encode_bhist I, fourierTransform_decode_encode_bhist R,
        fourierTransform_decode_encode_bhist V, fourierTransform_decode_encode_bhist H,
        fourierTransform_decode_encode_bhist C, fourierTransform_decode_encode_bhist P,
        fourierTransform_decode_encode_bhist N]

private theorem fourierTransformToEventFlow_injective {x y : FourierTransformUp} :
    fourierTransformToEventFlow x = fourierTransformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fourierTransformFromEventFlow (fourierTransformToEventFlow x) =
        fourierTransformFromEventFlow (fourierTransformToEventFlow y) :=
    congrArg fourierTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fourierTransform_round_trip x).symm
      (Eq.trans hread (fourierTransform_round_trip y)))

private theorem fourierTransformFields_faithful :
    ∀ x y : FourierTransformUp, fourierTransformFields x = fourierTransformFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 K1 I1 R1 V1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 K2 I2 R2 V2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance fourierTransformBHistCarrier : BHistCarrier FourierTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fourierTransformToEventFlow
  fromEventFlow := fourierTransformFromEventFlow

instance fourierTransformChapterTasteGate : ChapterTasteGate FourierTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fourierTransformFromEventFlow (fourierTransformToEventFlow x) = some x
    exact fourierTransform_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fourierTransformToEventFlow_injective heq)

instance fourierTransformFieldFaithful : FieldFaithful FourierTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fourierTransformFields
  field_faithful := fourierTransformFields_faithful

instance fourierTransformNontrivial : Nontrivial FourierTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FourierTransformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FourierTransformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FourierTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fourierTransformChapterTasteGate

end BEDC.Derived.FourierTransformUp
