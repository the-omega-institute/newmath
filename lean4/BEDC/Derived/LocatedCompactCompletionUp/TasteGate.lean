import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompactCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

namespace TasteGate

inductive LocatedCompactCompletionUp : Type where
  | mk (K T D S Q R F M H C P N : BHist) : LocatedCompactCompletionUp
  deriving DecidableEq

def locatedCompactCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompactCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompactCompletionEncodeBHist h

def locatedCompactCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompactCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompactCompletionDecodeBHist tail)

private theorem LocatedCompactCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompactCompletionFields : LocatedCompactCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompactCompletionUp.mk K T D S Q R F M H C P N =>
      [K, T, D, S, Q, R, F, M, H, C, P, N]

def locatedCompactCompletionToEventFlow : LocatedCompactCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCompactCompletionFields x).map locatedCompactCompletionEncodeBHist

private def locatedCompactCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompactCompletionEventAtDefault index rest

def locatedCompactCompletionFromEventFlow (ef : EventFlow) : Option LocatedCompactCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompactCompletionUp.mk
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 0 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 1 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 2 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 3 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 4 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 5 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 6 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 7 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 8 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 9 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 10 ef))
      (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEventAtDefault 11 ef)))

private theorem LocatedCompactCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompactCompletionUp,
      locatedCompactCompletionFromEventFlow (locatedCompactCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K T D S Q R F M H C P N =>
      change
        some
          (LocatedCompactCompletionUp.mk
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist K))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist T))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist D))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist S))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist Q))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist R))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist F))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist M))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist H))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist C))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist P))
            (locatedCompactCompletionDecodeBHist (locatedCompactCompletionEncodeBHist N))) =
          some (LocatedCompactCompletionUp.mk K T D S Q R F M H C P N)
      rw [LocatedCompactCompletionTasteGate_single_carrier_alignment_decode K,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode T,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode D,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode S,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode Q,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode R,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode F,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode M,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode H,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode C,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode P,
        LocatedCompactCompletionTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCompactCompletionTasteGate_single_carrier_alignment_injective
    {x y : LocatedCompactCompletionUp} :
    locatedCompactCompletionToEventFlow x = locatedCompactCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompactCompletionFromEventFlow (locatedCompactCompletionToEventFlow x) =
        locatedCompactCompletionFromEventFlow (locatedCompactCompletionToEventFlow y) :=
    congrArg locatedCompactCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCompactCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCompactCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedCompactCompletionTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedCompactCompletionUp,
      locatedCompactCompletionFields x = locatedCompactCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 T1 D1 S1 Q1 R1 F1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 T2 D2 S2 Q2 R2 F2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedCompactCompletionBHistCarrier : BHistCarrier LocatedCompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompactCompletionToEventFlow
  fromEventFlow := locatedCompactCompletionFromEventFlow

instance locatedCompactCompletionChapterTasteGate :
    ChapterTasteGate LocatedCompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompactCompletionFromEventFlow (locatedCompactCompletionToEventFlow x) =
      some x
    exact LocatedCompactCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCompactCompletionTasteGate_single_carrier_alignment_injective heq)

instance locatedCompactCompletionFieldFaithful : FieldFaithful LocatedCompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCompactCompletionFields
  field_faithful := LocatedCompactCompletionTasteGate_single_carrier_alignment_fields

instance locatedCompactCompletionNontrivial : Nontrivial LocatedCompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCompactCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LocatedCompactCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

end TasteGate

theorem LocatedCompactCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.locatedCompactCompletionDecodeBHist
        (TasteGate.locatedCompactCompletionEncodeBHist h) = h) ∧
      (∀ x : TasteGate.LocatedCompactCompletionUp,
        TasteGate.locatedCompactCompletionFromEventFlow
          (TasteGate.locatedCompactCompletionToEventFlow x) = some x) ∧
        (∀ x y : TasteGate.LocatedCompactCompletionUp,
          TasteGate.locatedCompactCompletionToEventFlow x =
            TasteGate.locatedCompactCompletionToEventFlow y →
            x = y) ∧
          TasteGate.locatedCompactCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨TasteGate.LocatedCompactCompletionTasteGate_single_carrier_alignment_decode,
      TasteGate.LocatedCompactCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        TasteGate.LocatedCompactCompletionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.LocatedCompactCompletionUp
