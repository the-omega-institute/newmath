import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformEntourageRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformEntourageRefinementUp : Type where
  | mk (R U epsilon delta B Y F S Q H C P N : BHist) : RealUniformEntourageRefinementUp
  deriving DecidableEq

def realUniformEntourageRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformEntourageRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformEntourageRefinementEncodeBHist h

def realUniformEntourageRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformEntourageRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformEntourageRefinementDecodeBHist tail)

private theorem RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realUniformEntourageRefinementDecodeBHist
      (realUniformEntourageRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformEntourageRefinementFields :
    RealUniformEntourageRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEntourageRefinementUp.mk R U epsilon delta B Y F S Q H C P N =>
      [R, U, epsilon, delta, B, Y, F, S, Q, H, C, P, N]

def realUniformEntourageRefinementToEventFlow :
    RealUniformEntourageRefinementUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (realUniformEntourageRefinementFields x).map realUniformEntourageRefinementEncodeBHist

private def realUniformEntourageRefinementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realUniformEntourageRefinementEventAtDefault index rest

def realUniformEntourageRefinementFromEventFlow
    (ef : EventFlow) : Option RealUniformEntourageRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealUniformEntourageRefinementUp.mk
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 0 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 1 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 2 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 3 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 4 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 5 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 6 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 7 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 8 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 9 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 10 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 11 ef))
      (realUniformEntourageRefinementDecodeBHist
        (realUniformEntourageRefinementEventAtDefault 12 ef)))

private theorem RealUniformEntourageRefinementTasteGate_single_carrier_alignment_round_trip
    (x : RealUniformEntourageRefinementUp) :
    realUniformEntourageRefinementFromEventFlow
        (realUniformEntourageRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R U epsilon delta B Y F S Q H C P N =>
      change
        some
          (RealUniformEntourageRefinementUp.mk
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist R))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist U))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist epsilon))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist delta))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist B))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist Y))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist F))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist S))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist Q))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist H))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist C))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist P))
            (realUniformEntourageRefinementDecodeBHist
              (realUniformEntourageRefinementEncodeBHist N))) =
          some (RealUniformEntourageRefinementUp.mk R U epsilon delta B Y F S Q H C P N)
      rw [RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode R,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode U,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode epsilon,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode delta,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode B,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode Y,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode F,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode S,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode Q,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode H,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode C,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode P,
        RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode N]

private theorem RealUniformEntourageRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealUniformEntourageRefinementUp} :
    realUniformEntourageRefinementToEventFlow x =
        realUniformEntourageRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformEntourageRefinementFromEventFlow
          (realUniformEntourageRefinementToEventFlow x) =
        realUniformEntourageRefinementFromEventFlow
          (realUniformEntourageRefinementToEventFlow y) :=
    congrArg realUniformEntourageRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealUniformEntourageRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealUniformEntourageRefinementTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealUniformEntourageRefinementTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealUniformEntourageRefinementUp,
      realUniformEntourageRefinementFields x = realUniformEntourageRefinementFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ U₁ epsilon₁ delta₁ B₁ Y₁ F₁ S₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ U₂ epsilon₂ delta₂ B₂ Y₂ F₂ S₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realUniformEntourageRefinementBHistCarrier :
    BHistCarrier RealUniformEntourageRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformEntourageRefinementToEventFlow
  fromEventFlow := realUniformEntourageRefinementFromEventFlow

instance realUniformEntourageRefinementChapterTasteGate :
    ChapterTasteGate RealUniformEntourageRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformEntourageRefinementFromEventFlow
      (realUniformEntourageRefinementToEventFlow x) = some x
    exact RealUniformEntourageRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealUniformEntourageRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realUniformEntourageRefinementFieldFaithful :
    FieldFaithful RealUniformEntourageRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformEntourageRefinementFields
  field_faithful := RealUniformEntourageRefinementTasteGate_single_carrier_alignment_fields

instance realUniformEntourageRefinementNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealUniformEntourageRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformEntourageRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealUniformEntourageRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformEntourageRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformEntourageRefinementChapterTasteGate

theorem RealUniformEntourageRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist, realUniformEntourageRefinementDecodeBHist
      (realUniformEntourageRefinementEncodeBHist h) = h) ∧
      (realUniformEntourageRefinementEncodeBHist BHist.Empty = ([] : List BMark)) ∧
        ChapterTasteGate RealUniformEntourageRefinementUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RealUniformEntourageRefinementTasteGate_single_carrier_alignment_decode, rfl,
      realUniformEntourageRefinementChapterTasteGate⟩

end BEDC.Derived.RealUniformEntourageRefinementUp
