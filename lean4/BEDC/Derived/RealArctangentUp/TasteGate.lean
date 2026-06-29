import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealArctangentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealArctangentUp : Type where
  | mk (X S R D E T Q H C P N : BHist) : RealArctangentUp
  deriving DecidableEq

def realArctangentFields : RealArctangentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealArctangentUp.mk X S R D E T Q H C P N =>
      [X, S, R, D, E, T, Q, H, C, P, N]

def realArctangentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realArctangentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realArctangentEncodeBHist h

def realArctangentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realArctangentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realArctangentDecodeBHist tail)

private theorem RealArctangentTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realArctangentDecodeBHist (realArctangentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realArctangentToEventFlow : RealArctangentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realArctangentFields x).map realArctangentEncodeBHist

private def realArctangentEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realArctangentEventAtDefault index rest

def realArctangentFromEventFlow (ef : EventFlow) : Option RealArctangentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealArctangentUp.mk
      (realArctangentDecodeBHist (realArctangentEventAtDefault 0 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 1 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 2 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 3 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 4 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 5 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 6 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 7 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 8 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 9 ef))
      (realArctangentDecodeBHist (realArctangentEventAtDefault 10 ef)))

private theorem RealArctangentTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealArctangentUp,
      realArctangentFromEventFlow (realArctangentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X S R D E T Q H C P N =>
      change
        some
          (RealArctangentUp.mk
            (realArctangentDecodeBHist (realArctangentEncodeBHist X))
            (realArctangentDecodeBHist (realArctangentEncodeBHist S))
            (realArctangentDecodeBHist (realArctangentEncodeBHist R))
            (realArctangentDecodeBHist (realArctangentEncodeBHist D))
            (realArctangentDecodeBHist (realArctangentEncodeBHist E))
            (realArctangentDecodeBHist (realArctangentEncodeBHist T))
            (realArctangentDecodeBHist (realArctangentEncodeBHist Q))
            (realArctangentDecodeBHist (realArctangentEncodeBHist H))
            (realArctangentDecodeBHist (realArctangentEncodeBHist C))
            (realArctangentDecodeBHist (realArctangentEncodeBHist P))
            (realArctangentDecodeBHist (realArctangentEncodeBHist N))) =
          some (RealArctangentUp.mk X S R D E T Q H C P N)
      rw [RealArctangentTasteGate_single_carrier_alignment_decode_encode X,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode S,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode R,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode D,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode E,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode T,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode Q,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode H,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode C,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode P,
        RealArctangentTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealArctangentTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealArctangentUp} :
    realArctangentToEventFlow x = realArctangentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realArctangentFromEventFlow (realArctangentToEventFlow x) =
        realArctangentFromEventFlow (realArctangentToEventFlow y) :=
    congrArg realArctangentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealArctangentTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealArctangentTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealArctangentTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealArctangentUp,
      realArctangentFields x = realArctangentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ S₁ R₁ D₁ E₁ T₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ S₂ R₂ D₂ E₂ T₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX t0
          injection t0 with hS t1
          injection t1 with hR t2
          injection t2 with hD t3
          injection t3 with hE t4
          injection t4 with hT t5
          injection t5 with hQ t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hX
          subst hS
          subst hR
          subst hD
          subst hE
          subst hT
          subst hQ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realArctangentBHistCarrier : BHistCarrier RealArctangentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realArctangentToEventFlow
  fromEventFlow := realArctangentFromEventFlow

instance realArctangentChapterTasteGate : ChapterTasteGate RealArctangentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realArctangentFromEventFlow (realArctangentToEventFlow x) = some x
    exact RealArctangentTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealArctangentTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realArctangentFieldFaithful : FieldFaithful RealArctangentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realArctangentFields
  field_faithful := RealArctangentTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate RealArctangentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realArctangentChapterTasteGate

theorem RealArctangentTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RealArctangentUp) ∧
      Nonempty (ChapterTasteGate RealArctangentUp) ∧
        Nonempty (FieldFaithful RealArctangentUp) ∧
          realArctangentEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            (∀ h : BHist,
              realArctangentDecodeBHist (realArctangentEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro realArctangentBHistCarrier,
      Nonempty.intro realArctangentChapterTasteGate,
      Nonempty.intro realArctangentFieldFaithful,
      rfl,
      RealArctangentTasteGate_single_carrier_alignment_decode_encode⟩

end BEDC.Derived.RealArctangentUp
