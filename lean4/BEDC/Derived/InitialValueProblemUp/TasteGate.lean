import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InitialValueProblemUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InitialValueProblemUp : Type where
  | mk (T X F W S E H C P N : BHist) : InitialValueProblemUp
  deriving DecidableEq

def initialValueProblemEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: initialValueProblemEncodeBHist h
  | BHist.e1 h => BMark.b1 :: initialValueProblemEncodeBHist h

def initialValueProblemDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (initialValueProblemDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (initialValueProblemDecodeBHist tail)

private theorem InitialValueProblemTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      initialValueProblemDecodeBHist (initialValueProblemEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def initialValueProblemFields : InitialValueProblemUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InitialValueProblemUp.mk T X F W S E H C P N => [T, X, F, W, S, E, H, C, P, N]

def initialValueProblemToEventFlow : InitialValueProblemUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (initialValueProblemFields x).map initialValueProblemEncodeBHist

private def initialValueProblemEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => initialValueProblemEventAt index rest

def initialValueProblemFromEventFlow (ef : EventFlow) : Option InitialValueProblemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (InitialValueProblemUp.mk
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 0 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 1 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 2 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 3 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 4 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 5 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 6 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 7 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 8 ef))
      (initialValueProblemDecodeBHist (initialValueProblemEventAt 9 ef)))

private theorem InitialValueProblemTasteGate_single_carrier_alignment_round_trip
    (x : InitialValueProblemUp) :
    initialValueProblemFromEventFlow (initialValueProblemToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T X F W S E H C P N =>
      change
        some
          (InitialValueProblemUp.mk
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist T))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist X))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist F))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist W))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist S))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist E))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist H))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist C))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist P))
            (initialValueProblemDecodeBHist (initialValueProblemEncodeBHist N))) =
          some (InitialValueProblemUp.mk T X F W S E H C P N)
      rw [InitialValueProblemTasteGate_single_carrier_alignment_decode_encode T,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode X,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode F,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode W,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode S,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode E,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode H,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode C,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode P,
        InitialValueProblemTasteGate_single_carrier_alignment_decode_encode N]

private theorem InitialValueProblemTasteGate_single_carrier_alignment_injective
    {x y : InitialValueProblemUp} :
    initialValueProblemToEventFlow x = initialValueProblemToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      initialValueProblemFromEventFlow (initialValueProblemToEventFlow x) =
        initialValueProblemFromEventFlow (initialValueProblemToEventFlow y) :=
    congrArg initialValueProblemFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (InitialValueProblemTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (InitialValueProblemTasteGate_single_carrier_alignment_round_trip y)))

private theorem InitialValueProblemTasteGate_single_carrier_alignment_fields :
    ∀ x y : InitialValueProblemUp,
      initialValueProblemFields x = initialValueProblemFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ X₁ F₁ W₁ S₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ X₂ F₂ W₂ S₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance initialValueProblemBHistCarrier : BHistCarrier InitialValueProblemUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := initialValueProblemToEventFlow
  fromEventFlow := initialValueProblemFromEventFlow

instance initialValueProblemChapterTasteGate : ChapterTasteGate InitialValueProblemUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change initialValueProblemFromEventFlow (initialValueProblemToEventFlow x) = some x
    exact InitialValueProblemTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (InitialValueProblemTasteGate_single_carrier_alignment_injective heq)

instance initialValueProblemFieldFaithful : FieldFaithful InitialValueProblemUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := initialValueProblemFields
  field_faithful := InitialValueProblemTasteGate_single_carrier_alignment_fields

instance initialValueProblemNontrivial :
    BEDC.Meta.TasteGate.Nontrivial InitialValueProblemUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InitialValueProblemUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InitialValueProblemUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def InitialValueProblemTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate InitialValueProblemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  initialValueProblemChapterTasteGate

theorem InitialValueProblemTasteGate_single_carrier_alignment :
    (∀ h : BHist, initialValueProblemDecodeBHist (initialValueProblemEncodeBHist h) = h) ∧
      (∀ x : InitialValueProblemUp,
        initialValueProblemFromEventFlow (initialValueProblemToEventFlow x) = some x) ∧
        (∀ x y : InitialValueProblemUp,
          initialValueProblemToEventFlow x = initialValueProblemToEventFlow y → x = y) ∧
          initialValueProblemEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact InitialValueProblemTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact InitialValueProblemTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact InitialValueProblemTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.InitialValueProblemUp
