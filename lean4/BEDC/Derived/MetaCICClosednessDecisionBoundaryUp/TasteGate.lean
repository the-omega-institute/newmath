import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICClosednessDecisionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICClosednessDecisionBoundaryUp : Type where
  | mk (A Q F S Z O H C P N : BHist) : MetaCICClosednessDecisionBoundaryUp

def metaCICClosednessDecisionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICClosednessDecisionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICClosednessDecisionBoundaryEncodeBHist h

def metaCICClosednessDecisionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICClosednessDecisionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICClosednessDecisionBoundaryDecodeBHist tail)

private theorem metaCICClosednessDecisionBoundaryDecode_encode :
    ∀ h : BHist,
      metaCICClosednessDecisionBoundaryDecodeBHist
          (metaCICClosednessDecisionBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICClosednessDecisionBoundaryFields :
    MetaCICClosednessDecisionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICClosednessDecisionBoundaryUp.mk A Q F S Z O H C P N =>
      [A, Q, F, S, Z, O, H, C, P, N]

def metaCICClosednessDecisionBoundaryToEventFlow :
    MetaCICClosednessDecisionBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (metaCICClosednessDecisionBoundaryFields x).map
      metaCICClosednessDecisionBoundaryEncodeBHist

private def metaCICClosednessDecisionBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metaCICClosednessDecisionBoundaryEventAtDefault index rest

def metaCICClosednessDecisionBoundaryFromEventFlow
    (ef : EventFlow) : Option MetaCICClosednessDecisionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICClosednessDecisionBoundaryUp.mk
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 0 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 1 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 2 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 3 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 4 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 5 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 6 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 7 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 8 ef))
      (metaCICClosednessDecisionBoundaryDecodeBHist
        (metaCICClosednessDecisionBoundaryEventAtDefault 9 ef)))

private theorem metaCICClosednessDecisionBoundary_round_trip :
    ∀ x : MetaCICClosednessDecisionBoundaryUp,
      metaCICClosednessDecisionBoundaryFromEventFlow
          (metaCICClosednessDecisionBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q F S Z O H C P N =>
      change
        some
          (MetaCICClosednessDecisionBoundaryUp.mk
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist A))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist Q))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist F))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist S))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist Z))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist O))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist H))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist C))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist P))
            (metaCICClosednessDecisionBoundaryDecodeBHist
              (metaCICClosednessDecisionBoundaryEncodeBHist N))) =
          some (MetaCICClosednessDecisionBoundaryUp.mk A Q F S Z O H C P N)
      rw [metaCICClosednessDecisionBoundaryDecode_encode A,
        metaCICClosednessDecisionBoundaryDecode_encode Q,
        metaCICClosednessDecisionBoundaryDecode_encode F,
        metaCICClosednessDecisionBoundaryDecode_encode S,
        metaCICClosednessDecisionBoundaryDecode_encode Z,
        metaCICClosednessDecisionBoundaryDecode_encode O,
        metaCICClosednessDecisionBoundaryDecode_encode H,
        metaCICClosednessDecisionBoundaryDecode_encode C,
        metaCICClosednessDecisionBoundaryDecode_encode P,
        metaCICClosednessDecisionBoundaryDecode_encode N]

private theorem metaCICClosednessDecisionBoundaryToEventFlow_injective
    {x y : MetaCICClosednessDecisionBoundaryUp} :
    metaCICClosednessDecisionBoundaryToEventFlow x =
        metaCICClosednessDecisionBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICClosednessDecisionBoundaryFromEventFlow
          (metaCICClosednessDecisionBoundaryToEventFlow x) =
        metaCICClosednessDecisionBoundaryFromEventFlow
          (metaCICClosednessDecisionBoundaryToEventFlow y) :=
    congrArg metaCICClosednessDecisionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICClosednessDecisionBoundary_round_trip x).symm
      (Eq.trans hread (metaCICClosednessDecisionBoundary_round_trip y)))

private theorem metaCICClosednessDecisionBoundary_fields_faithful :
    ∀ x y : MetaCICClosednessDecisionBoundaryUp,
      metaCICClosednessDecisionBoundaryFields x =
          metaCICClosednessDecisionBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ Q₁ F₁ S₁ Z₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ Q₂ F₂ S₂ Z₂ O₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hA t0
          injection t0 with hQ t1
          injection t1 with hF t2
          injection t2 with hS t3
          injection t3 with hZ t4
          injection t4 with hO t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          subst hA
          subst hQ
          subst hF
          subst hS
          subst hZ
          subst hO
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance metaCICClosednessDecisionBoundaryBHistCarrier :
    BHistCarrier MetaCICClosednessDecisionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICClosednessDecisionBoundaryToEventFlow
  fromEventFlow := metaCICClosednessDecisionBoundaryFromEventFlow

instance metaCICClosednessDecisionBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICClosednessDecisionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICClosednessDecisionBoundaryFromEventFlow
          (metaCICClosednessDecisionBoundaryToEventFlow x) =
        some x
    exact metaCICClosednessDecisionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICClosednessDecisionBoundaryToEventFlow_injective heq)

instance metaCICClosednessDecisionBoundaryFieldFaithful :
    FieldFaithful MetaCICClosednessDecisionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICClosednessDecisionBoundaryFields
  field_faithful := metaCICClosednessDecisionBoundary_fields_faithful

instance metaCICClosednessDecisionBoundaryNontrivial :
    Nontrivial MetaCICClosednessDecisionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICClosednessDecisionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICClosednessDecisionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def metaCICClosednessDecisionBoundary_taste_gate :
    ChapterTasteGate MetaCICClosednessDecisionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICClosednessDecisionBoundaryChapterTasteGate

theorem MetaCICClosednessDecisionBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metaCICClosednessDecisionBoundaryDecodeBHist
          (metaCICClosednessDecisionBoundaryEncodeBHist h) = h) /\
      (forall x : MetaCICClosednessDecisionBoundaryUp,
        metaCICClosednessDecisionBoundaryFromEventFlow
            (metaCICClosednessDecisionBoundaryToEventFlow x) = some x) /\
      (forall x y : MetaCICClosednessDecisionBoundaryUp,
        metaCICClosednessDecisionBoundaryToEventFlow x =
            metaCICClosednessDecisionBoundaryToEventFlow y ->
          x = y) /\
      metaCICClosednessDecisionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICClosednessDecisionBoundaryDecode_encode
  · constructor
    · exact metaCICClosednessDecisionBoundary_round_trip
    · constructor
      · intro x y heq
        exact metaCICClosednessDecisionBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICClosednessDecisionBoundaryUp
