import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowRealSealAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowRealSealAuditUp : Type where
  | mk (W D R E F H C P N : BHist) : FiniteWindowRealSealAuditUp
  deriving DecidableEq

def finiteWindowRealSealAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowRealSealAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowRealSealAuditEncodeBHist h

def finiteWindowRealSealAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowRealSealAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowRealSealAuditDecodeBHist tail)

private theorem FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteWindowRealSealAuditToEventFlow :
    FiniteWindowRealSealAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowRealSealAuditUp.mk W D R E F H C P N =>
      [[BMark.b0],
        finiteWindowRealSealAuditEncodeBHist W,
        [BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteWindowRealSealAuditEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist N]

private def finiteWindowRealSealAuditEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteWindowRealSealAuditEventAtDefault index rest

def finiteWindowRealSealAuditFromEventFlow
    (ef : EventFlow) : Option FiniteWindowRealSealAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteWindowRealSealAuditUp.mk
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 1 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 3 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 5 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 7 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 9 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 11 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 13 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 15 ef))
      (finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEventAtDefault 17 ef)))

private theorem FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteWindowRealSealAuditUp,
      finiteWindowRealSealAuditFromEventFlow
        (finiteWindowRealSealAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W D R E F H C P N =>
      change
        some
          (FiniteWindowRealSealAuditUp.mk
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist W))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist D))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist R))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist E))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist F))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist H))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist C))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist P))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist N))) =
          some (FiniteWindowRealSealAuditUp.mk W D R E F H C P N)
      rw [FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode W,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode D,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode R,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode E,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode F,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode H,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode C,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode P,
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode N]

private theorem FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_injective
    {x y : FiniteWindowRealSealAuditUp} :
    finiteWindowRealSealAuditToEventFlow x =
      finiteWindowRealSealAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowRealSealAuditFromEventFlow
          (finiteWindowRealSealAuditToEventFlow x) =
        finiteWindowRealSealAuditFromEventFlow
          (finiteWindowRealSealAuditToEventFlow y) :=
    congrArg finiteWindowRealSealAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_round_trip y)))

private def finiteWindowRealSealAuditFields :
    FiniteWindowRealSealAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowRealSealAuditUp.mk W D R E F H C P N => [W, D, R, E, F, H, C, P, N]

private theorem FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteWindowRealSealAuditUp,
      finiteWindowRealSealAuditFields x = finiteWindowRealSealAuditFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 D1 R1 E1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 D2 R2 E2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteWindowRealSealAuditBHistCarrier :
    BHistCarrier FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowRealSealAuditToEventFlow
  fromEventFlow := finiteWindowRealSealAuditFromEventFlow

instance finiteWindowRealSealAuditChapterTasteGate :
    ChapterTasteGate FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteWindowRealSealAuditFromEventFlow
        (finiteWindowRealSealAuditToEventFlow x) = some x
    exact FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FiniteWindowRealSealAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowRealSealAuditChapterTasteGate

instance finiteWindowRealSealAuditFieldFaithful :
    FieldFaithful FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowRealSealAuditFields
  field_faithful := FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_fields

instance finiteWindowRealSealAuditNontrivial :
    Nontrivial FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowRealSealAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteWindowRealSealAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteWindowRealSealAuditTasteGate_single_carrier_alignment :
    finiteWindowRealSealAuditEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      finiteWindowRealSealAuditEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] ∧
        (∀ h : BHist,
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist h) = h) ∧
          (∀ x : FiniteWindowRealSealAuditUp,
            finiteWindowRealSealAuditFromEventFlow
              (finiteWindowRealSealAuditToEventFlow x) = some x) ∧
            (∀ x y : FiniteWindowRealSealAuditUp,
              finiteWindowRealSealAuditToEventFlow x =
                finiteWindowRealSealAuditToEventFlow y → x = y) ∧
              Nonempty (FieldFaithful FiniteWindowRealSealAuditUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl, rfl,
      FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_decode,
      FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteWindowRealSealAuditTasteGate_single_carrier_alignment_injective heq),
      ⟨finiteWindowRealSealAuditFieldFaithful⟩⟩

end BEDC.Derived.FiniteWindowRealSealAuditUp
