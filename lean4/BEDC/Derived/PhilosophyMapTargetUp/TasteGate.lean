import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhilosophyMapTargetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhilosophyMapTargetUp : Type where
  | mk : (R G K S A X H C P N : BHist) → PhilosophyMapTargetUp
  deriving DecidableEq

def philosophyMapTargetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: philosophyMapTargetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: philosophyMapTargetEncodeBHist h

def philosophyMapTargetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (philosophyMapTargetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (philosophyMapTargetDecodeBHist tail)

private theorem philosophyMapTargetDecode_encode_bhist :
    ∀ h : BHist, philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def philosophyMapTargetFields : PhilosophyMapTargetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyMapTargetUp.mk R G K S A X H C P N => [R, G, K, S, A, X, H, C, P, N]

def philosophyMapTargetToEventFlow : PhilosophyMapTargetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (philosophyMapTargetFields x).map philosophyMapTargetEncodeBHist

private def philosophyMapTargetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => philosophyMapTargetEventAtDefault index rest

def philosophyMapTargetFromEventFlow (ef : EventFlow) : Option PhilosophyMapTargetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhilosophyMapTargetUp.mk
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 0 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 1 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 2 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 3 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 4 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 5 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 6 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 7 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 8 ef))
      (philosophyMapTargetDecodeBHist (philosophyMapTargetEventAtDefault 9 ef)))

private theorem philosophyMapTarget_round_trip :
    ∀ x : PhilosophyMapTargetUp,
      philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R G K S A X H C P N =>
      change
        some
          (PhilosophyMapTargetUp.mk
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist R))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist G))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist K))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist S))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist A))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist X))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist H))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist C))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist P))
            (philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist N))) =
          some (PhilosophyMapTargetUp.mk R G K S A X H C P N)
      rw [philosophyMapTargetDecode_encode_bhist R,
        philosophyMapTargetDecode_encode_bhist G,
        philosophyMapTargetDecode_encode_bhist K,
        philosophyMapTargetDecode_encode_bhist S,
        philosophyMapTargetDecode_encode_bhist A,
        philosophyMapTargetDecode_encode_bhist X,
        philosophyMapTargetDecode_encode_bhist H,
        philosophyMapTargetDecode_encode_bhist C,
        philosophyMapTargetDecode_encode_bhist P,
        philosophyMapTargetDecode_encode_bhist N]

private theorem philosophyMapTargetToEventFlow_injective {x y : PhilosophyMapTargetUp} :
    philosophyMapTargetToEventFlow x = philosophyMapTargetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) =
        philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow y) :=
    congrArg philosophyMapTargetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (philosophyMapTarget_round_trip x).symm
      (Eq.trans hread (philosophyMapTarget_round_trip y)))

private theorem philosophyMapTarget_fields_faithful :
    ∀ x y : PhilosophyMapTargetUp, philosophyMapTargetFields x = philosophyMapTargetFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ G₁ K₁ S₁ A₁ X₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ G₂ K₂ S₂ A₂ X₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance philosophyMapTargetBHistCarrier : BHistCarrier PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := philosophyMapTargetToEventFlow
  fromEventFlow := philosophyMapTargetFromEventFlow

instance philosophyMapTargetChapterTasteGate : ChapterTasteGate PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := philosophyMapTarget_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (philosophyMapTargetToEventFlow_injective heq)

instance philosophyMapTargetFieldFaithful : FieldFaithful PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := philosophyMapTargetFields
  field_faithful := philosophyMapTarget_fields_faithful

instance philosophyMapTargetNontrivial : Nontrivial PhilosophyMapTargetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhilosophyMapTargetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhilosophyMapTargetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhilosophyMapTargetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophyMapTargetChapterTasteGate

theorem PhilosophyMapTargetTasteGate_single_carrier_alignment :
    (∀ h : BHist, philosophyMapTargetDecodeBHist (philosophyMapTargetEncodeBHist h) = h) ∧
      (∀ x : PhilosophyMapTargetUp,
        philosophyMapTargetFromEventFlow (philosophyMapTargetToEventFlow x) = some x) ∧
        (∀ x y : PhilosophyMapTargetUp,
          philosophyMapTargetToEventFlow x = philosophyMapTargetToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful PhilosophyMapTargetUp) ∧
            philosophyMapTargetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact philosophyMapTargetDecode_encode_bhist
  · constructor
    · exact philosophyMapTarget_round_trip
    · constructor
      · intro x y heq
        exact philosophyMapTargetToEventFlow_injective heq
      · constructor
        · exact ⟨philosophyMapTargetFieldFaithful⟩
        · rfl

end BEDC.Derived.PhilosophyMapTargetUp.TasteGate
