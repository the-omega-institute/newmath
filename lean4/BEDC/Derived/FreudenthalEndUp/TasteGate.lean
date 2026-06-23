import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FreudenthalEndUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FreudenthalEndUp : Type where
  | mk (X E C₀ C₁ T R H Q P N : BHist) : FreudenthalEndUp
  deriving DecidableEq

def freudenthalEndEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: freudenthalEndEncodeBHist h
  | BHist.e1 h => BMark.b1 :: freudenthalEndEncodeBHist h

def freudenthalEndDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (freudenthalEndDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (freudenthalEndDecodeBHist tail)

private theorem freudenthalEndDecode_encode_bhist :
    ∀ h : BHist, freudenthalEndDecodeBHist (freudenthalEndEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def freudenthalEndFields : FreudenthalEndUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FreudenthalEndUp.mk X E C₀ C₁ T R H Q P N =>
      [X, E, C₀, C₁, T, R, H, Q, P, N]

def freudenthalEndToEventFlow : FreudenthalEndUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (freudenthalEndFields x).map freudenthalEndEncodeBHist

private def freudenthalEndEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      freudenthalEndEventAtDefault index rest

def freudenthalEndFromEventFlow (ef : EventFlow) : Option FreudenthalEndUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FreudenthalEndUp.mk
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 0 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 1 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 2 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 3 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 4 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 5 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 6 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 7 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 8 ef))
      (freudenthalEndDecodeBHist (freudenthalEndEventAtDefault 9 ef)))

private theorem freudenthalEnd_round_trip (x : FreudenthalEndUp) :
    freudenthalEndFromEventFlow (freudenthalEndToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X E C₀ C₁ T R H Q P N =>
      change
        some
          (FreudenthalEndUp.mk
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist X))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist E))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist C₀))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist C₁))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist T))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist R))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist H))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist Q))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist P))
            (freudenthalEndDecodeBHist (freudenthalEndEncodeBHist N))) =
          some (FreudenthalEndUp.mk X E C₀ C₁ T R H Q P N)
      rw [freudenthalEndDecode_encode_bhist X, freudenthalEndDecode_encode_bhist E,
        freudenthalEndDecode_encode_bhist C₀, freudenthalEndDecode_encode_bhist C₁,
        freudenthalEndDecode_encode_bhist T, freudenthalEndDecode_encode_bhist R,
        freudenthalEndDecode_encode_bhist H, freudenthalEndDecode_encode_bhist Q,
        freudenthalEndDecode_encode_bhist P, freudenthalEndDecode_encode_bhist N]

private theorem freudenthalEndToEventFlow_injective {x y : FreudenthalEndUp} :
    freudenthalEndToEventFlow x = freudenthalEndToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      freudenthalEndFromEventFlow (freudenthalEndToEventFlow x) =
        freudenthalEndFromEventFlow (freudenthalEndToEventFlow y) :=
    congrArg freudenthalEndFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (freudenthalEnd_round_trip x).symm
      (Eq.trans hread (freudenthalEnd_round_trip y)))

instance freudenthalEndBHistCarrier : BHistCarrier FreudenthalEndUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := freudenthalEndToEventFlow
  fromEventFlow := freudenthalEndFromEventFlow

instance freudenthalEndChapterTasteGate : ChapterTasteGate FreudenthalEndUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change freudenthalEndFromEventFlow (freudenthalEndToEventFlow x) = some x
    exact freudenthalEnd_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (freudenthalEndToEventFlow_injective heq)

instance freudenthalEndFieldFaithful : FieldFaithful FreudenthalEndUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := freudenthalEndFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk X₁ E₁ C₀₁ C₁₁ T₁ R₁ H₁ Q₁ P₁ N₁ =>
        cases y with
        | mk X₂ E₂ C₀₂ C₁₂ T₂ R₂ H₂ Q₂ P₂ N₂ =>
            cases hfields
            rfl

instance freudenthalEndNontrivial : Nontrivial FreudenthalEndUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FreudenthalEndUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FreudenthalEndUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FreudenthalEndUp :=
  -- BEDC touchpoint anchor: BHist BMark
  freudenthalEndChapterTasteGate

theorem FreudenthalEndTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FreudenthalEndUp) ∧
      Nonempty (FieldFaithful FreudenthalEndUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FreudenthalEndUp) ∧
          freudenthalEndEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ h : BHist, freudenthalEndDecodeBHist (freudenthalEndEncodeBHist h) = h) ∧
              (∀ x : FreudenthalEndUp,
                freudenthalEndFromEventFlow (freudenthalEndToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨freudenthalEndChapterTasteGate⟩
  · constructor
    · exact ⟨freudenthalEndFieldFaithful⟩
    · constructor
      · exact ⟨freudenthalEndNontrivial⟩
      · constructor
        · rfl
        · constructor
          · intro h
            exact freudenthalEndDecode_encode_bhist h
          · intro x
            exact freudenthalEnd_round_trip x

end BEDC.Derived.FreudenthalEndUp
