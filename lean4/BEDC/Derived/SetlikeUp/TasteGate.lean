import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SetlikeUp : Type where
  | mk (M Q I R E H C P N : BHist) : SetlikeUp
  deriving DecidableEq

def setlikeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: setlikeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: setlikeEncodeBHist h

def setlikeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (setlikeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (setlikeDecodeBHist tail)

private theorem SetlikeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, setlikeDecodeBHist (setlikeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def setlikeFields : SetlikeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SetlikeUp.mk M Q I R E H C P N => [M, Q, I, R, E, H, C, P, N]

def setlikeToEventFlow : SetlikeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (setlikeFields x).map setlikeEncodeBHist

private def setlikeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => setlikeEventAtDefault index rest

def setlikeFromEventFlow (ef : EventFlow) : Option SetlikeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SetlikeUp.mk
      (setlikeDecodeBHist (setlikeEventAtDefault 0 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 1 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 2 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 3 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 4 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 5 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 6 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 7 ef))
      (setlikeDecodeBHist (setlikeEventAtDefault 8 ef)))

private theorem SetlikeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SetlikeUp, setlikeFromEventFlow (setlikeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M Q I R E H C P N =>
      change
        some
          (SetlikeUp.mk
            (setlikeDecodeBHist (setlikeEncodeBHist M))
            (setlikeDecodeBHist (setlikeEncodeBHist Q))
            (setlikeDecodeBHist (setlikeEncodeBHist I))
            (setlikeDecodeBHist (setlikeEncodeBHist R))
            (setlikeDecodeBHist (setlikeEncodeBHist E))
            (setlikeDecodeBHist (setlikeEncodeBHist H))
            (setlikeDecodeBHist (setlikeEncodeBHist C))
            (setlikeDecodeBHist (setlikeEncodeBHist P))
            (setlikeDecodeBHist (setlikeEncodeBHist N))) =
          some (SetlikeUp.mk M Q I R E H C P N)
      rw [SetlikeTasteGate_single_carrier_alignment_decode M,
        SetlikeTasteGate_single_carrier_alignment_decode Q,
        SetlikeTasteGate_single_carrier_alignment_decode I,
        SetlikeTasteGate_single_carrier_alignment_decode R,
        SetlikeTasteGate_single_carrier_alignment_decode E,
        SetlikeTasteGate_single_carrier_alignment_decode H,
        SetlikeTasteGate_single_carrier_alignment_decode C,
        SetlikeTasteGate_single_carrier_alignment_decode P,
        SetlikeTasteGate_single_carrier_alignment_decode N]

private theorem SetlikeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SetlikeUp} :
    setlikeToEventFlow x = setlikeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      setlikeFromEventFlow (setlikeToEventFlow x) =
        setlikeFromEventFlow (setlikeToEventFlow y) :=
    congrArg setlikeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SetlikeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SetlikeTasteGate_single_carrier_alignment_round_trip y)))

private theorem SetlikeTasteGate_single_carrier_alignment_fields :
    ∀ x y : SetlikeUp, setlikeFields x = setlikeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ Q₁ I₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ Q₂ I₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance setlikeBHistCarrier : BHistCarrier SetlikeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := setlikeToEventFlow
  fromEventFlow := setlikeFromEventFlow

instance setlikeChapterTasteGate : ChapterTasteGate SetlikeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change setlikeFromEventFlow (setlikeToEventFlow x) = some x
    exact SetlikeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SetlikeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance setlikeFieldFaithful : FieldFaithful SetlikeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := setlikeFields
  field_faithful := SetlikeTasteGate_single_carrier_alignment_fields

instance setlikeNontrivial : Nontrivial SetlikeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SetlikeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SetlikeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SetlikeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  setlikeChapterTasteGate

theorem SetlikeTasteGate_single_carrier_alignment :
    (∀ h : BHist, setlikeDecodeBHist (setlikeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SetlikeUp) ∧ Nonempty (ChapterTasteGate SetlikeUp) ∧
        setlikeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SetlikeTasteGate_single_carrier_alignment_decode,
      ⟨setlikeBHistCarrier⟩, ⟨setlikeChapterTasteGate⟩, rfl⟩

end BEDC.Derived.SetlikeUp
