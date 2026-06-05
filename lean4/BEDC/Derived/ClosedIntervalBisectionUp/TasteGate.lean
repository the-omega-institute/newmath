import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalBisectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalBisectionUp : Type where
  | mk (I L M D S R E H C P N : BHist) : ClosedIntervalBisectionUp
  deriving DecidableEq

def closedIntervalBisectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalBisectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalBisectionEncodeBHist h

def closedIntervalBisectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalBisectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalBisectionDecodeBHist tail)

private theorem ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedIntervalBisectionDecodeBHist
        (closedIntervalBisectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalBisectionFields : ClosedIntervalBisectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalBisectionUp.mk I L M D S R E H C P N =>
      [I, L, M, D, S, R, E, H, C, P, N]

def closedIntervalBisectionToEventFlow : ClosedIntervalBisectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedIntervalBisectionFields x).map closedIntervalBisectionEncodeBHist

private def closedIntervalBisectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedIntervalBisectionEventAt index rest

def closedIntervalBisectionFromEventFlow
    (ef : EventFlow) : Option ClosedIntervalBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedIntervalBisectionUp.mk
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 0 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 1 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 2 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 3 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 4 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 5 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 6 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 7 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 8 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 9 ef))
      (closedIntervalBisectionDecodeBHist (closedIntervalBisectionEventAt 10 ef)))

private theorem ClosedIntervalBisectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedIntervalBisectionUp,
      closedIntervalBisectionFromEventFlow
        (closedIntervalBisectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I L M D S R E H C P N =>
      change
        some
          (ClosedIntervalBisectionUp.mk
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist I))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist L))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist M))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist D))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist S))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist R))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist E))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist H))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist C))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist P))
            (closedIntervalBisectionDecodeBHist
              (closedIntervalBisectionEncodeBHist N))) =
          some (ClosedIntervalBisectionUp.mk I L M D S R E H C P N)
      rw [ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode I,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode L,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode M,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode D,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode S,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode R,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode E,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode H,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode C,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode P,
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode N]

private theorem ClosedIntervalBisectionTasteGate_single_carrier_alignment_injective
    {x y : ClosedIntervalBisectionUp} :
    closedIntervalBisectionToEventFlow x =
        closedIntervalBisectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalBisectionFromEventFlow
          (closedIntervalBisectionToEventFlow x) =
        closedIntervalBisectionFromEventFlow
          (closedIntervalBisectionToEventFlow y) :=
    congrArg closedIntervalBisectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedIntervalBisectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedIntervalBisectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedIntervalBisectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : ClosedIntervalBisectionUp,
      closedIntervalBisectionFields x = closedIntervalBisectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 L1 M1 D1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 L2 M2 D2 S2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance closedIntervalBisectionBHistCarrier : BHistCarrier ClosedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalBisectionToEventFlow
  fromEventFlow := closedIntervalBisectionFromEventFlow

instance closedIntervalBisectionChapterTasteGate :
    ChapterTasteGate ClosedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalBisectionFromEventFlow
        (closedIntervalBisectionToEventFlow x) = some x
    exact ClosedIntervalBisectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedIntervalBisectionTasteGate_single_carrier_alignment_injective heq)

instance closedIntervalBisectionFieldFaithful :
    FieldFaithful ClosedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedIntervalBisectionFields
  field_faithful := ClosedIntervalBisectionTasteGate_single_carrier_alignment_fields

instance closedIntervalBisectionNontrivial : Nontrivial ClosedIntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedIntervalBisectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ClosedIntervalBisectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedIntervalBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedIntervalBisectionChapterTasteGate

theorem ClosedIntervalBisectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedIntervalBisectionDecodeBHist (closedIntervalBisectionEncodeBHist h) = h) ∧
      (∀ x : ClosedIntervalBisectionUp,
        closedIntervalBisectionFromEventFlow
          (closedIntervalBisectionToEventFlow x) = some x) ∧
        (∀ x y : ClosedIntervalBisectionUp,
          closedIntervalBisectionToEventFlow x =
              closedIntervalBisectionToEventFlow y →
            x = y) ∧
          closedIntervalBisectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ClosedIntervalBisectionTasteGate_single_carrier_alignment_decode,
      ClosedIntervalBisectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ClosedIntervalBisectionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.ClosedIntervalBisectionUp
