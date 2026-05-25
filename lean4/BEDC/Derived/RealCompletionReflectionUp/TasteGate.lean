import BEDC.Derived.RealCompletionReflectionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realCompletionReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionReflectionEncodeBHist h

def realCompletionReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionReflectionDecodeBHist tail)

private theorem RealCompletionReflectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realCompletionReflectionDecodeBHist
      (realCompletionReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCompletionReflectionFields : RealCompletionReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionReflectionUp.mk C R S D E F H K P N => [C, R, S, D, E, F, H, K, P, N]

def realCompletionReflectionToEventFlow : RealCompletionReflectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realCompletionReflectionFields x).map realCompletionReflectionEncodeBHist

private def realCompletionReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCompletionReflectionEventAtDefault index rest

def realCompletionReflectionFromEventFlow (ef : EventFlow) : Option RealCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCompletionReflectionUp.mk
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 0 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 1 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 2 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 3 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 4 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 5 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 6 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 7 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 8 ef))
      (realCompletionReflectionDecodeBHist (realCompletionReflectionEventAtDefault 9 ef)))

private theorem RealCompletionReflectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealCompletionReflectionUp,
      realCompletionReflectionFromEventFlow
        (realCompletionReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk C R S D E F H K P N =>
      change
        some
          (RealCompletionReflectionUp.mk
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist C))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist R))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist S))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist D))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist E))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist F))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist H))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist K))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist P))
            (realCompletionReflectionDecodeBHist (realCompletionReflectionEncodeBHist N))) =
          some (RealCompletionReflectionUp.mk C R S D E F H K P N)
      rw [RealCompletionReflectionTasteGate_single_carrier_alignment_decode C,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode R,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode S,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode D,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode E,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode F,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode H,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode K,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode P,
        RealCompletionReflectionTasteGate_single_carrier_alignment_decode N]

private theorem RealCompletionReflectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealCompletionReflectionUp} :
    realCompletionReflectionToEventFlow x = realCompletionReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionReflectionFromEventFlow (realCompletionReflectionToEventFlow x) =
        realCompletionReflectionFromEventFlow (realCompletionReflectionToEventFlow y) :=
    congrArg realCompletionReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealCompletionReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealCompletionReflectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealCompletionReflectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealCompletionReflectionUp, realCompletionReflectionFields x =
      realCompletionReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 R1 S1 D1 E1 F1 H1 K1 P1 N1 =>
      cases y with
      | mk C2 R2 S2 D2 E2 F2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance realCompletionReflectionBHistCarrier : BHistCarrier RealCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionReflectionToEventFlow
  fromEventFlow := realCompletionReflectionFromEventFlow

instance realCompletionReflectionChapterTasteGate :
    ChapterTasteGate RealCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletionReflectionFromEventFlow (realCompletionReflectionToEventFlow x) = some x
    exact RealCompletionReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealCompletionReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realCompletionReflectionFieldFaithful : FieldFaithful RealCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCompletionReflectionFields
  field_faithful := RealCompletionReflectionTasteGate_single_carrier_alignment_fields

instance realCompletionReflectionNontrivial : Nontrivial RealCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletionReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletionReflectionChapterTasteGate

theorem RealCompletionReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, realCompletionReflectionDecodeBHist
        (realCompletionReflectionEncodeBHist h) = h) ∧
      (∀ x : RealCompletionReflectionUp,
        realCompletionReflectionFromEventFlow (realCompletionReflectionToEventFlow x) = some x) ∧
        (∀ x y : RealCompletionReflectionUp,
          realCompletionReflectionToEventFlow x = realCompletionReflectionToEventFlow y → x = y) ∧
          realCompletionReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealCompletionReflectionTasteGate_single_carrier_alignment_decode,
      RealCompletionReflectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealCompletionReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealCompletionReflectionUp
