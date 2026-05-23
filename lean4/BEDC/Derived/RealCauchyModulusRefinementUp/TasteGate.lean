import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyModulusRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyModulusRefinementUp : Type where
  | mk (M0 M1 R S0 S1 D0 D1 Q E H C P N : BHist) : RealCauchyModulusRefinementUp
  deriving DecidableEq

def realCauchyModulusRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyModulusRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyModulusRefinementEncodeBHist h

def realCauchyModulusRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyModulusRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyModulusRefinementDecodeBHist tail)

private theorem realCauchyModulusRefinement_decode_encode :
    ∀ h : BHist,
      realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyModulusRefinementFields : RealCauchyModulusRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyModulusRefinementUp.mk M0 M1 R S0 S1 D0 D1 Q E H C P N =>
      [M0, M1, R, S0, S1, D0, D1, Q, E, H, C, P, N]

def realCauchyModulusRefinementToEventFlow : RealCauchyModulusRefinementUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realCauchyModulusRefinementFields x).map realCauchyModulusRefinementEncodeBHist

private def realCauchyModulusRefinementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyModulusRefinementEventAtDefault index rest

def realCauchyModulusRefinementFromEventFlow :
    EventFlow → Option RealCauchyModulusRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealCauchyModulusRefinementUp.mk
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 0 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 1 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 2 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 3 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 4 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 5 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 6 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 7 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 8 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 9 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 10 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 11 ef))
        (realCauchyModulusRefinementDecodeBHist
          (realCauchyModulusRefinementEventAtDefault 12 ef)))

private theorem realCauchyModulusRefinement_round_trip :
    ∀ x : RealCauchyModulusRefinementUp,
      realCauchyModulusRefinementFromEventFlow
          (realCauchyModulusRefinementToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M0 M1 R S0 S1 D0 D1 Q E H C P N =>
      change
        some
          (RealCauchyModulusRefinementUp.mk
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist M0))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist M1))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist R))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist S0))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist S1))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist D0))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist D1))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist Q))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist E))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist H))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist C))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist P))
            (realCauchyModulusRefinementDecodeBHist
              (realCauchyModulusRefinementEncodeBHist N))) =
          some (RealCauchyModulusRefinementUp.mk M0 M1 R S0 S1 D0 D1 Q E H C P N)
      rw [realCauchyModulusRefinement_decode_encode M0,
        realCauchyModulusRefinement_decode_encode M1,
        realCauchyModulusRefinement_decode_encode R,
        realCauchyModulusRefinement_decode_encode S0,
        realCauchyModulusRefinement_decode_encode S1,
        realCauchyModulusRefinement_decode_encode D0,
        realCauchyModulusRefinement_decode_encode D1,
        realCauchyModulusRefinement_decode_encode Q,
        realCauchyModulusRefinement_decode_encode E,
        realCauchyModulusRefinement_decode_encode H,
        realCauchyModulusRefinement_decode_encode C,
        realCauchyModulusRefinement_decode_encode P,
        realCauchyModulusRefinement_decode_encode N]

private theorem realCauchyModulusRefinement_toEventFlow_injective
    {x y : RealCauchyModulusRefinementUp} :
    realCauchyModulusRefinementToEventFlow x =
        realCauchyModulusRefinementToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyModulusRefinementFromEventFlow
          (realCauchyModulusRefinementToEventFlow x) =
        realCauchyModulusRefinementFromEventFlow
          (realCauchyModulusRefinementToEventFlow y) :=
    congrArg realCauchyModulusRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyModulusRefinement_round_trip x).symm
      (Eq.trans hread (realCauchyModulusRefinement_round_trip y)))

private theorem realCauchyModulusRefinement_field_faithful :
    ∀ x y : RealCauchyModulusRefinementUp,
      realCauchyModulusRefinementFields x = realCauchyModulusRefinementFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M0₁ M1₁ R₁ S0₁ S1₁ D0₁ D1₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M0₂ M1₂ R₂ S0₂ S1₂ D0₂ D1₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance realCauchyModulusRefinementBHistCarrier :
    BHistCarrier RealCauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyModulusRefinementToEventFlow
  fromEventFlow := realCauchyModulusRefinementFromEventFlow

instance realCauchyModulusRefinementChapterTasteGate :
    ChapterTasteGate RealCauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCauchyModulusRefinementFromEventFlow
          (realCauchyModulusRefinementToEventFlow x) =
        some x
    exact realCauchyModulusRefinement_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyModulusRefinement_toEventFlow_injective heq)

instance realCauchyModulusRefinementFieldFaithful :
    FieldFaithful RealCauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCauchyModulusRefinementFields
  field_faithful := realCauchyModulusRefinement_field_faithful

instance realCauchyModulusRefinementNontrivial :
    Nontrivial RealCauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCauchyModulusRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealCauchyModulusRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCauchyModulusRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyModulusRefinementChapterTasteGate

theorem RealCauchyModulusRefinementTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealCauchyModulusRefinementUp) ∧
      Nonempty (FieldFaithful RealCauchyModulusRefinementUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RealCauchyModulusRefinementUp) ∧
      realCauchyModulusRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨realCauchyModulusRefinementChapterTasteGate⟩,
      ⟨realCauchyModulusRefinementFieldFaithful⟩,
      ⟨realCauchyModulusRefinementNontrivial⟩,
      rfl⟩

end BEDC.Derived.RealCauchyModulusRefinementUp
