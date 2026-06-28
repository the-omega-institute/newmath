import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegralCompletionModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannIntegralCompletionModulusUp : Type where
  | mk (I G D R E H C P N : BHist) : RiemannIntegralCompletionModulusUp
  deriving DecidableEq

def riemannIntegralCompletionModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannIntegralCompletionModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannIntegralCompletionModulusEncodeBHist h

def riemannIntegralCompletionModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannIntegralCompletionModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannIntegralCompletionModulusDecodeBHist tail)

private theorem RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannIntegralCompletionModulusFields :
    RiemannIntegralCompletionModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegralCompletionModulusUp.mk I G D R E H C P N => [I, G, D, R, E, H, C, P, N]

def riemannIntegralCompletionModulusToEventFlow :
    RiemannIntegralCompletionModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (riemannIntegralCompletionModulusFields x).map
        riemannIntegralCompletionModulusEncodeBHist

private def riemannIntegralCompletionModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannIntegralCompletionModulusEventAt index rest

def riemannIntegralCompletionModulusFromEventFlow
    (ef : EventFlow) : Option RiemannIntegralCompletionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannIntegralCompletionModulusUp.mk
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 0 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 1 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 2 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 3 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 4 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 5 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 6 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 7 ef))
      (riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEventAt 8 ef)))

private theorem RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_round_trip
    (x : RiemannIntegralCompletionModulusUp) :
    riemannIntegralCompletionModulusFromEventFlow
      (riemannIntegralCompletionModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I G D R E H C P N =>
      change
        some
          (RiemannIntegralCompletionModulusUp.mk
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist I))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist G))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist D))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist R))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist E))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist H))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist C))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist P))
            (riemannIntegralCompletionModulusDecodeBHist
              (riemannIntegralCompletionModulusEncodeBHist N))) =
          some (RiemannIntegralCompletionModulusUp.mk I G D R E H C P N)
      rw [RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode I,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode G,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode D,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode R,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode E,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode H,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode C,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode P,
        RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannIntegralCompletionModulusUp} :
    riemannIntegralCompletionModulusToEventFlow x =
      riemannIntegralCompletionModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannIntegralCompletionModulusFromEventFlow
          (riemannIntegralCompletionModulusToEventFlow x) =
        riemannIntegralCompletionModulusFromEventFlow
          (riemannIntegralCompletionModulusToEventFlow y) :=
    congrArg riemannIntegralCompletionModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : RiemannIntegralCompletionModulusUp,
      riemannIntegralCompletionModulusFields x =
        riemannIntegralCompletionModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ G₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ G₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance riemannIntegralCompletionModulusBHistCarrier :
    BHistCarrier RiemannIntegralCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannIntegralCompletionModulusToEventFlow
  fromEventFlow := riemannIntegralCompletionModulusFromEventFlow

instance riemannIntegralCompletionModulusChapterTasteGate :
    ChapterTasteGate RiemannIntegralCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      riemannIntegralCompletionModulusFromEventFlow
        (riemannIntegralCompletionModulusToEventFlow x) = some x
    exact RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance riemannIntegralCompletionModulusFieldFaithful :
    FieldFaithful RiemannIntegralCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannIntegralCompletionModulusFields
  field_faithful := RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_fields

instance riemannIntegralCompletionModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RiemannIntegralCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannIntegralCompletionModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RiemannIntegralCompletionModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RiemannIntegralCompletionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannIntegralCompletionModulusChapterTasteGate

theorem RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      riemannIntegralCompletionModulusDecodeBHist
        (riemannIntegralCompletionModulusEncodeBHist h) = h) ∧
      (∀ x : RiemannIntegralCompletionModulusUp,
        riemannIntegralCompletionModulusFromEventFlow
          (riemannIntegralCompletionModulusToEventFlow x) = some x) ∧
        (∀ x y : RiemannIntegralCompletionModulusUp,
          riemannIntegralCompletionModulusToEventFlow x =
            riemannIntegralCompletionModulusToEventFlow y → x = y) ∧
          riemannIntegralCompletionModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact RiemannIntegralCompletionModulusTasteGate_single_carrier_alignment_toEventFlow_injective
      heq
  · rfl

end BEDC.Derived.RiemannIntegralCompletionModulusUp
