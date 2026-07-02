import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareRecurrenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareRecurrenceUp : Type where
  | mk (D E P M A W T H C Q N : BHist) : PoincareRecurrenceUp
  deriving DecidableEq

def poincareRecurrenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareRecurrenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareRecurrenceEncodeBHist h

def poincareRecurrenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareRecurrenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareRecurrenceDecodeBHist tail)

private theorem PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def poincareRecurrenceFields : PoincareRecurrenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareRecurrenceUp.mk D E P M A W T H C Q N => [D, E, P, M, A, W, T, H, C, Q, N]

def poincareRecurrenceToEventFlow : PoincareRecurrenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poincareRecurrenceFields x).map poincareRecurrenceEncodeBHist

private def poincareRecurrenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => poincareRecurrenceEventAt index rest

def poincareRecurrenceFromEventFlow : EventFlow → Option PoincareRecurrenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (PoincareRecurrenceUp.mk
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 0 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 1 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 2 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 3 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 4 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 5 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 6 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 7 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 8 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 9 ef))
          (poincareRecurrenceDecodeBHist (poincareRecurrenceEventAt 10 ef)))

private theorem PoincareRecurrenceTasteGate_single_carrier_alignment_round_trip
    (x : PoincareRecurrenceUp) :
    poincareRecurrenceFromEventFlow (poincareRecurrenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D E P M A W T H C Q N =>
      change
        some
            (PoincareRecurrenceUp.mk
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist D))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist E))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist P))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist M))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist A))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist W))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist T))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist H))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist C))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist Q))
              (poincareRecurrenceDecodeBHist (poincareRecurrenceEncodeBHist N))) =
          some (PoincareRecurrenceUp.mk D E P M A W T H C Q N)
      rw [PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode D,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode E,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode P,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode M,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode A,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode W,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode T,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode H,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode C,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode Q,
        PoincareRecurrenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem PoincareRecurrenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PoincareRecurrenceUp} :
    poincareRecurrenceToEventFlow x = poincareRecurrenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareRecurrenceFromEventFlow (poincareRecurrenceToEventFlow x) =
        poincareRecurrenceFromEventFlow (poincareRecurrenceToEventFlow y) :=
    congrArg poincareRecurrenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PoincareRecurrenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PoincareRecurrenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem PoincareRecurrenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : PoincareRecurrenceUp,
      poincareRecurrenceFields x = poincareRecurrenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ E₁ P₁ M₁ A₁ W₁ T₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk D₂ E₂ P₂ M₂ A₂ W₂ T₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance poincareRecurrenceBHistCarrier : BHistCarrier PoincareRecurrenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareRecurrenceToEventFlow
  fromEventFlow := poincareRecurrenceFromEventFlow

instance poincareRecurrenceChapterTasteGate :
    ChapterTasteGate PoincareRecurrenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change poincareRecurrenceFromEventFlow (poincareRecurrenceToEventFlow x) = some x
    exact PoincareRecurrenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PoincareRecurrenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance poincareRecurrenceFieldFaithful : FieldFaithful PoincareRecurrenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := poincareRecurrenceFields
  field_faithful := PoincareRecurrenceTasteGate_single_carrier_alignment_fields

instance poincareRecurrenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PoincareRecurrenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PoincareRecurrenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PoincareRecurrenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem PoincareRecurrenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PoincareRecurrenceUp) ∧
      Nonempty (ChapterTasteGate PoincareRecurrenceUp) ∧
        Nonempty (FieldFaithful PoincareRecurrenceUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial PoincareRecurrenceUp) ∧
            (∀ x : PoincareRecurrenceUp,
              poincareRecurrenceFromEventFlow (poincareRecurrenceToEventFlow x) = some x) ∧
              poincareRecurrenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨poincareRecurrenceBHistCarrier⟩
  constructor
  · exact ⟨poincareRecurrenceChapterTasteGate⟩
  constructor
  · exact ⟨poincareRecurrenceFieldFaithful⟩
  constructor
  · exact ⟨poincareRecurrenceNontrivial⟩
  constructor
  · exact PoincareRecurrenceTasteGate_single_carrier_alignment_round_trip
  · rfl

end BEDC.Derived.PoincareRecurrenceUp
