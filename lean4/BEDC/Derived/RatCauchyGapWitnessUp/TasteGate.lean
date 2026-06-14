import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RatCauchyGapWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RatCauchyGapWitnessUp : Type where
  | mk (L U D W R E H C P N : BHist) : RatCauchyGapWitnessUp
  deriving DecidableEq

def ratCauchyGapWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ratCauchyGapWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ratCauchyGapWitnessEncodeBHist h

def ratCauchyGapWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ratCauchyGapWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ratCauchyGapWitnessDecodeBHist tail)

private theorem RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def ratCauchyGapWitnessFields : RatCauchyGapWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RatCauchyGapWitnessUp.mk L U D W R E H C P N => [L, U, D, W, R, E, H, C, P, N]

def ratCauchyGapWitnessToEventFlow : RatCauchyGapWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ratCauchyGapWitnessFields x).map ratCauchyGapWitnessEncodeBHist

private def ratCauchyGapWitnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ratCauchyGapWitnessEventAt index rest

def ratCauchyGapWitnessFromEventFlow (ef : EventFlow) : Option RatCauchyGapWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RatCauchyGapWitnessUp.mk
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 0 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 1 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 2 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 3 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 4 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 5 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 6 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 7 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 8 ef))
      (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEventAt 9 ef)))

private theorem RatCauchyGapWitnessTasteGate_single_carrier_alignment_round_trip
    (x : RatCauchyGapWitnessUp) :
    ratCauchyGapWitnessFromEventFlow (ratCauchyGapWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U D W R E H C P N =>
      change
        some
          (RatCauchyGapWitnessUp.mk
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist L))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist U))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist D))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist W))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist R))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist E))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist H))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist C))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist P))
            (ratCauchyGapWitnessDecodeBHist (ratCauchyGapWitnessEncodeBHist N))) =
          some (RatCauchyGapWitnessUp.mk L U D W R E H C P N)
      rw [RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode L,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode U,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode D,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode W,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode R,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode E,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode H,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode C,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode P,
        RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem RatCauchyGapWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RatCauchyGapWitnessUp} :
    ratCauchyGapWitnessToEventFlow x = ratCauchyGapWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ratCauchyGapWitnessFromEventFlow (ratCauchyGapWitnessToEventFlow x) =
        ratCauchyGapWitnessFromEventFlow (ratCauchyGapWitnessToEventFlow y) :=
    congrArg ratCauchyGapWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RatCauchyGapWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RatCauchyGapWitnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem RatCauchyGapWitnessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RatCauchyGapWitnessUp, ratCauchyGapWitnessFields x = ratCauchyGapWitnessFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ U₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ U₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hL tail0
          injection tail0 with hU tail1
          injection tail1 with hD tail2
          injection tail2 with hW tail3
          injection tail3 with hR tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hL
          subst hU
          subst hD
          subst hW
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance ratCauchyGapWitnessBHistCarrier : BHistCarrier RatCauchyGapWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ratCauchyGapWitnessToEventFlow
  fromEventFlow := ratCauchyGapWitnessFromEventFlow

instance ratCauchyGapWitnessChapterTasteGate : ChapterTasteGate RatCauchyGapWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ratCauchyGapWitnessFromEventFlow (ratCauchyGapWitnessToEventFlow x) = some x
    exact RatCauchyGapWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RatCauchyGapWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ratCauchyGapWitnessFieldFaithful : FieldFaithful RatCauchyGapWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ratCauchyGapWitnessFields
  field_faithful := RatCauchyGapWitnessTasteGate_single_carrier_alignment_fields_faithful

theorem RatCauchyGapWitnessTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RatCauchyGapWitnessUp) ∧
      Nonempty (ChapterTasteGate RatCauchyGapWitnessUp) ∧
        Nonempty (FieldFaithful RatCauchyGapWitnessUp) ∧
          (∀ h : BHist, ratCauchyGapWitnessDecodeBHist
            (ratCauchyGapWitnessEncodeBHist h) = h) ∧
            (∀ x : RatCauchyGapWitnessUp,
              ratCauchyGapWitnessFromEventFlow (ratCauchyGapWitnessToEventFlow x) = some x) ∧
              ratCauchyGapWitnessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨ratCauchyGapWitnessBHistCarrier⟩, ⟨ratCauchyGapWitnessChapterTasteGate⟩,
      ⟨ratCauchyGapWitnessFieldFaithful⟩,
      RatCauchyGapWitnessTasteGate_single_carrier_alignment_decode_encode,
      RatCauchyGapWitnessTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.RatCauchyGapWitnessUp
