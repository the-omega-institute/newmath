import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteIntervalChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteIntervalChoiceUp : Type where
  | mk (K Q L W R D E H C P N : BHist) : FiniteIntervalChoiceUp
  deriving DecidableEq

def finiteIntervalChoiceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteIntervalChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteIntervalChoiceEncodeBHist h

def finiteIntervalChoiceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteIntervalChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteIntervalChoiceDecodeBHist tail)

private theorem FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode :
    forall h : BHist, finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteIntervalChoiceToEventFlow : FiniteIntervalChoiceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteIntervalChoiceUp.mk K Q L W R D E H C P N =>
      [finiteIntervalChoiceEncodeBHist K,
        finiteIntervalChoiceEncodeBHist Q,
        finiteIntervalChoiceEncodeBHist L,
        finiteIntervalChoiceEncodeBHist W,
        finiteIntervalChoiceEncodeBHist R,
        finiteIntervalChoiceEncodeBHist D,
        finiteIntervalChoiceEncodeBHist E,
        finiteIntervalChoiceEncodeBHist H,
        finiteIntervalChoiceEncodeBHist C,
        finiteIntervalChoiceEncodeBHist P,
        finiteIntervalChoiceEncodeBHist N]

private def finiteIntervalChoiceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteIntervalChoiceEventAtDefault index rest

def finiteIntervalChoiceFromEventFlow (ef : EventFlow) : Option FiniteIntervalChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteIntervalChoiceUp.mk
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 0 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 1 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 2 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 3 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 4 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 5 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 6 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 7 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 8 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 9 ef))
      (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEventAtDefault 10 ef)))

private theorem FiniteIntervalChoiceTasteGate_single_carrier_alignment_round_trip
    (x : FiniteIntervalChoiceUp) :
    finiteIntervalChoiceFromEventFlow (finiteIntervalChoiceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K Q L W R D E H C P N =>
      change
        some
          (FiniteIntervalChoiceUp.mk
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist K))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist Q))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist L))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist W))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist R))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist D))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist E))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist H))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist C))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist P))
            (finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist N))) =
          some (FiniteIntervalChoiceUp.mk K Q L W R D E H C P N)
      rw [FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode K,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode Q,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode L,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode W,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode R,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode D,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode E,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode H,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode C,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode P,
        FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode N]

private theorem FiniteIntervalChoiceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteIntervalChoiceUp} :
    finiteIntervalChoiceToEventFlow x = finiteIntervalChoiceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteIntervalChoiceFromEventFlow (finiteIntervalChoiceToEventFlow x) =
        finiteIntervalChoiceFromEventFlow (finiteIntervalChoiceToEventFlow y) :=
    congrArg finiteIntervalChoiceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteIntervalChoiceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteIntervalChoiceTasteGate_single_carrier_alignment_round_trip y)))

private def finiteIntervalChoiceFields : FiniteIntervalChoiceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteIntervalChoiceUp.mk K Q L W R D E H C P N => [K, Q, L, W, R, D, E, H, C, P, N]

private theorem FiniteIntervalChoiceTasteGate_single_carrier_alignment_fields :
    forall x y : FiniteIntervalChoiceUp, finiteIntervalChoiceFields x =
      finiteIntervalChoiceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 Q1 L1 W1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 Q2 L2 W2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteIntervalChoiceBHistCarrier : BHistCarrier FiniteIntervalChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteIntervalChoiceToEventFlow
  fromEventFlow := finiteIntervalChoiceFromEventFlow

instance finiteIntervalChoiceChapterTasteGate : ChapterTasteGate FiniteIntervalChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteIntervalChoiceFromEventFlow (finiteIntervalChoiceToEventFlow x) = some x
    exact FiniteIntervalChoiceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteIntervalChoiceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteIntervalChoiceFieldFaithful : FieldFaithful FiniteIntervalChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteIntervalChoiceFields
  field_faithful := FiniteIntervalChoiceTasteGate_single_carrier_alignment_fields

instance finiteIntervalChoiceNontrivial : Nontrivial FiniteIntervalChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteIntervalChoiceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteIntervalChoiceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteIntervalChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteIntervalChoiceChapterTasteGate

theorem FiniteIntervalChoiceTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteIntervalChoiceDecodeBHist (finiteIntervalChoiceEncodeBHist h) = h) ∧
      (∀ x : FiniteIntervalChoiceUp,
        finiteIntervalChoiceFromEventFlow (finiteIntervalChoiceToEventFlow x) = some x) ∧
        (∀ x y : FiniteIntervalChoiceUp,
          finiteIntervalChoiceToEventFlow x = finiteIntervalChoiceToEventFlow y -> x = y) ∧
          finiteIntervalChoiceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FiniteIntervalChoiceTasteGate_single_carrier_alignment_decode,
      FiniteIntervalChoiceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FiniteIntervalChoiceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteIntervalChoiceUp
