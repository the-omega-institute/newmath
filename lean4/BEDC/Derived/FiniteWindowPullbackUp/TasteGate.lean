import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowPullbackUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowPullbackUp : Type where
  | mk (S R D E H C P N : BHist) : FiniteWindowPullbackUp
  deriving DecidableEq

def finiteWindowPullbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowPullbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowPullbackEncodeBHist h

def finiteWindowPullbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowPullbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowPullbackDecodeBHist tail)

private theorem finiteWindowPullbackDecode_encode_bhist :
    ∀ h : BHist, finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteWindowPullbackToEventFlow : FiniteWindowPullbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowPullbackUp.mk S R D E H C P N =>
      [[BMark.b0],
        finiteWindowPullbackEncodeBHist S,
        [BMark.b1, BMark.b0],
        finiteWindowPullbackEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteWindowPullbackEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowPullbackEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowPullbackEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowPullbackEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowPullbackEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteWindowPullbackEncodeBHist N]

private def finiteWindowPullbackEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteWindowPullbackEventAtDefault index rest

def finiteWindowPullbackFromEventFlow (ef : EventFlow) : Option FiniteWindowPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteWindowPullbackUp.mk
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 1 ef))
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 3 ef))
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 5 ef))
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 7 ef))
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 9 ef))
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 11 ef))
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 13 ef))
      (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEventAtDefault 15 ef)))

private theorem finiteWindowPullback_round_trip :
    ∀ x : FiniteWindowPullbackUp,
      finiteWindowPullbackFromEventFlow (finiteWindowPullbackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D E H C P N =>
      change
        some
          (FiniteWindowPullbackUp.mk
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist S))
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist R))
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist D))
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist E))
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist H))
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist C))
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist P))
            (finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist N))) =
          some (FiniteWindowPullbackUp.mk S R D E H C P N)
      rw [finiteWindowPullbackDecode_encode_bhist S, finiteWindowPullbackDecode_encode_bhist R,
        finiteWindowPullbackDecode_encode_bhist D, finiteWindowPullbackDecode_encode_bhist E,
        finiteWindowPullbackDecode_encode_bhist H, finiteWindowPullbackDecode_encode_bhist C,
        finiteWindowPullbackDecode_encode_bhist P, finiteWindowPullbackDecode_encode_bhist N]

private theorem finiteWindowPullbackToEventFlow_injective {x y : FiniteWindowPullbackUp} :
    finiteWindowPullbackToEventFlow x = finiteWindowPullbackToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowPullbackFromEventFlow (finiteWindowPullbackToEventFlow x) =
        finiteWindowPullbackFromEventFlow (finiteWindowPullbackToEventFlow y) :=
    congrArg finiteWindowPullbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteWindowPullback_round_trip x).symm
      (Eq.trans hread (finiteWindowPullback_round_trip y)))

private def finiteWindowPullbackFields : FiniteWindowPullbackUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowPullbackUp.mk S R D E H C P N => [S, R, D, E, H, C, P, N]

private theorem finiteWindowPullbackFields_faithful :
    ∀ x y : FiniteWindowPullbackUp, finiteWindowPullbackFields x = finiteWindowPullbackFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteWindowPullbackBHistCarrier : BHistCarrier FiniteWindowPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowPullbackToEventFlow
  fromEventFlow := finiteWindowPullbackFromEventFlow

instance finiteWindowPullbackChapterTasteGate : ChapterTasteGate FiniteWindowPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteWindowPullbackFromEventFlow (finiteWindowPullbackToEventFlow x) = some x
    exact finiteWindowPullback_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowPullbackToEventFlow_injective heq)

instance finiteWindowPullbackFieldFaithful : FieldFaithful FiniteWindowPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowPullbackFields
  field_faithful := finiteWindowPullbackFields_faithful

instance finiteWindowPullbackNontrivial : BEDC.Meta.TasteGate.Nontrivial FiniteWindowPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowPullbackUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FiniteWindowPullbackUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteWindowPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowPullbackChapterTasteGate

theorem FiniteWindowPullbackTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteWindowPullbackUp) ∧
      Nonempty (FieldFaithful FiniteWindowPullbackUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteWindowPullbackUp) ∧
          (∀ h : BHist,
            finiteWindowPullbackDecodeBHist (finiteWindowPullbackEncodeBHist h) = h) ∧
            (∀ x : FiniteWindowPullbackUp,
              finiteWindowPullbackFromEventFlow (finiteWindowPullbackToEventFlow x) = some x) ∧
              (∀ x y : FiniteWindowPullbackUp,
                finiteWindowPullbackToEventFlow x = finiteWindowPullbackToEventFlow y → x = y) ∧
                finiteWindowPullbackEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨finiteWindowPullbackChapterTasteGate⟩,
      ⟨finiteWindowPullbackFieldFaithful⟩,
      ⟨finiteWindowPullbackNontrivial⟩,
      finiteWindowPullbackDecode_encode_bhist,
      finiteWindowPullback_round_trip,
      (fun _ _ heq => finiteWindowPullbackToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteWindowPullbackUp
