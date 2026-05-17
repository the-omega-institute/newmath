import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalRecordInvariantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalRecordInvariantUp : Type where
  | mk (r i o h c p n : BHist) : PhysicalRecordInvariantUp
  deriving DecidableEq

def physicalRecordInvariantEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalRecordInvariantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalRecordInvariantEncodeBHist h

def physicalRecordInvariantDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalRecordInvariantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalRecordInvariantDecodeBHist tail)

private theorem physicalRecordInvariant_decode_encode_bhist :
    ∀ h : BHist,
      physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem physicalRecordInvariant_mk_congr
    {R R' I I' O O' H H' C C' P P' N N' : BHist}
    (hR : R' = R) (hI : I' = I) (hO : O' = O) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    PhysicalRecordInvariantUp.mk R' I' O' H' C' P' N' =
      PhysicalRecordInvariantUp.mk R I O H C P N := by
  cases hR
  cases hI
  cases hO
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def physicalRecordInvariantFields : PhysicalRecordInvariantUp → List BHist
  | PhysicalRecordInvariantUp.mk r i o h c p n => [r, i, o, h, c, p, n]

def physicalRecordInvariantToEventFlow : PhysicalRecordInvariantUp → EventFlow
  | PhysicalRecordInvariantUp.mk r i o h c p n =>
      [physicalRecordInvariantEncodeBHist r,
        physicalRecordInvariantEncodeBHist i,
        physicalRecordInvariantEncodeBHist o,
        physicalRecordInvariantEncodeBHist h,
        physicalRecordInvariantEncodeBHist c,
        physicalRecordInvariantEncodeBHist p,
        physicalRecordInvariantEncodeBHist n]

private def physicalRecordInvariantEventAtDefault : Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => physicalRecordInvariantEventAtDefault index rest

def physicalRecordInvariantFromEventFlow (ef : EventFlow) : Option PhysicalRecordInvariantUp :=
  some
    (PhysicalRecordInvariantUp.mk
      (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEventAtDefault 0 ef))
      (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEventAtDefault 1 ef))
      (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEventAtDefault 2 ef))
      (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEventAtDefault 3 ef))
      (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEventAtDefault 4 ef))
      (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEventAtDefault 5 ef))
      (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEventAtDefault 6 ef)))

private theorem physicalRecordInvariant_round_trip :
    ∀ x : PhysicalRecordInvariantUp,
      physicalRecordInvariantFromEventFlow (physicalRecordInvariantToEventFlow x) = some x := by
  intro x
  cases x with
  | mk r i o h c p n =>
      change
        some
          (PhysicalRecordInvariantUp.mk
            (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist r))
            (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist i))
            (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist o))
            (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist h))
            (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist c))
            (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist p))
            (physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist n))) =
          some (PhysicalRecordInvariantUp.mk r i o h c p n)
      rw [physicalRecordInvariant_decode_encode_bhist r,
        physicalRecordInvariant_decode_encode_bhist i,
        physicalRecordInvariant_decode_encode_bhist o,
        physicalRecordInvariant_decode_encode_bhist h,
        physicalRecordInvariant_decode_encode_bhist c,
        physicalRecordInvariant_decode_encode_bhist p,
        physicalRecordInvariant_decode_encode_bhist n]

private theorem physicalRecordInvariantToEventFlow_injective
    {x y : PhysicalRecordInvariantUp} :
    physicalRecordInvariantToEventFlow x = physicalRecordInvariantToEventFlow y → x = y := by
  intro heq
  have hread :
      physicalRecordInvariantFromEventFlow (physicalRecordInvariantToEventFlow x) =
        physicalRecordInvariantFromEventFlow (physicalRecordInvariantToEventFlow y) :=
    congrArg physicalRecordInvariantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalRecordInvariant_round_trip x).symm
      (Eq.trans hread (physicalRecordInvariant_round_trip y)))

private theorem physicalRecordInvariant_field_faithful :
    ∀ x y : PhysicalRecordInvariantUp,
      physicalRecordInvariantFields x = physicalRecordInvariantFields y → x = y := by
  intro x y hfields
  cases x with
  | mk r i o h c p n =>
      cases y with
      | mk r' i' o' h' c' p' n' =>
          cases hfields
          rfl

instance physicalRecordInvariantBHistCarrier : BHistCarrier PhysicalRecordInvariantUp where
  toEventFlow := physicalRecordInvariantToEventFlow
  fromEventFlow := physicalRecordInvariantFromEventFlow

instance physicalRecordInvariantChapterTasteGate : ChapterTasteGate PhysicalRecordInvariantUp where
  round_trip := by
    intro x
    change physicalRecordInvariantFromEventFlow (physicalRecordInvariantToEventFlow x) = some x
    exact physicalRecordInvariant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalRecordInvariantToEventFlow_injective heq)

instance physicalRecordInvariantFieldFaithful : FieldFaithful PhysicalRecordInvariantUp where
  fields := physicalRecordInvariantFields
  field_faithful := physicalRecordInvariant_field_faithful

instance physicalRecordInvariantNontrivial : Nontrivial PhysicalRecordInvariantUp where
  witness_pair :=
    ⟨PhysicalRecordInvariantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalRecordInvariantUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalRecordInvariantUp :=
  physicalRecordInvariantChapterTasteGate

theorem PhysicalRecordInvariantTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PhysicalRecordInvariantUp) ∧
      Nonempty (FieldFaithful PhysicalRecordInvariantUp) ∧
        Nonempty (Nontrivial PhysicalRecordInvariantUp) ∧
          (∀ h : BHist,
            physicalRecordInvariantDecodeBHist (physicalRecordInvariantEncodeBHist h) = h) ∧
            (∀ x : PhysicalRecordInvariantUp,
              physicalRecordInvariantFromEventFlow
                  (physicalRecordInvariantToEventFlow x) =
                some x) ∧
              (∀ x y : PhysicalRecordInvariantUp,
                physicalRecordInvariantToEventFlow x = physicalRecordInvariantToEventFlow y →
                  x = y) ∧
                physicalRecordInvariantEncodeBHist BHist.Empty = ([] : RawEvent) := by
  exact
    ⟨⟨physicalRecordInvariantChapterTasteGate⟩,
      ⟨physicalRecordInvariantFieldFaithful⟩,
      ⟨physicalRecordInvariantNontrivial⟩,
      physicalRecordInvariant_decode_encode_bhist,
      physicalRecordInvariant_round_trip,
      (fun _ _ heq => physicalRecordInvariantToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PhysicalRecordInvariantUp
