import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedCauchyRealSectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedCauchyRealSectionUp : Type where
  | mk (I T W R D E H C P N : BHist) : NestedCauchyRealSectionUp
  deriving DecidableEq

def nestedCauchyRealSectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedCauchyRealSectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedCauchyRealSectionEncodeBHist h

def nestedCauchyRealSectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedCauchyRealSectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedCauchyRealSectionDecodeBHist tail)

private theorem NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedCauchyRealSectionFields : NestedCauchyRealSectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedCauchyRealSectionUp.mk I T W R D E H C P N => [I, T, W, R, D, E, H, C, P, N]

def nestedCauchyRealSectionToEventFlow : NestedCauchyRealSectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (nestedCauchyRealSectionFields x).map nestedCauchyRealSectionEncodeBHist

private def nestedCauchyRealSectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedCauchyRealSectionEventAtDefault index rest

def nestedCauchyRealSectionFromEventFlow
    (ef : EventFlow) : Option NestedCauchyRealSectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedCauchyRealSectionUp.mk
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 0 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 1 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 2 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 3 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 4 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 5 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 6 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 7 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 8 ef))
      (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEventAtDefault 9 ef)))

private theorem NestedCauchyRealSectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedCauchyRealSectionUp,
      nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I T W R D E H C P N =>
      change
        some
          (NestedCauchyRealSectionUp.mk
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist I))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist T))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist W))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist R))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist D))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist E))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist H))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist C))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist P))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist N))) =
          some (NestedCauchyRealSectionUp.mk I T W R D E H C P N)
      rw [NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode I,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode T,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode W,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode R,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode D,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode E,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode H,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode C,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode P,
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode N]

private theorem NestedCauchyRealSectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedCauchyRealSectionUp} :
    nestedCauchyRealSectionToEventFlow x = nestedCauchyRealSectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow x) =
        nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow y) :=
    congrArg nestedCauchyRealSectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (NestedCauchyRealSectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedCauchyRealSectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem NestedCauchyRealSectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : NestedCauchyRealSectionUp,
      nestedCauchyRealSectionFields x = nestedCauchyRealSectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 T1 W1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 T2 W2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance nestedCauchyRealSectionBHistCarrier : BHistCarrier NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedCauchyRealSectionToEventFlow
  fromEventFlow := nestedCauchyRealSectionFromEventFlow

instance nestedCauchyRealSectionChapterTasteGate :
    ChapterTasteGate NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow x) = some x
    exact NestedCauchyRealSectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (NestedCauchyRealSectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nestedCauchyRealSectionFieldFaithful :
    FieldFaithful NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedCauchyRealSectionFields
  field_faithful := NestedCauchyRealSectionTasteGate_single_carrier_alignment_fields

instance nestedCauchyRealSectionNontrivial : Nontrivial NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedCauchyRealSectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedCauchyRealSectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedCauchyRealSectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedCauchyRealSectionChapterTasteGate

theorem NestedCauchyRealSectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist h) = h) ∧
      (∀ x : NestedCauchyRealSectionUp,
        nestedCauchyRealSectionFromEventFlow
          (nestedCauchyRealSectionToEventFlow x) = some x) ∧
        (∀ x y : NestedCauchyRealSectionUp,
          nestedCauchyRealSectionToEventFlow x =
            nestedCauchyRealSectionToEventFlow y → x = y) ∧
          nestedCauchyRealSectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨NestedCauchyRealSectionTasteGate_single_carrier_alignment_decode,
      NestedCauchyRealSectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        NestedCauchyRealSectionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NestedCauchyRealSectionUp
