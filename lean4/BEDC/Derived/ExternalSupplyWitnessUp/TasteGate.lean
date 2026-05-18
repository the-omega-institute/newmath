import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplyWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplyWitnessUp : Type where
  | mk (S R G L H C P N : BHist) : ExternalSupplyWitnessUp
  deriving DecidableEq

def externalSupplyWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplyWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplyWitnessEncodeBHist h

def externalSupplyWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplyWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplyWitnessDecodeBHist tail)

private theorem ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem externalSupplyWitness_mk_congr
    {S S' R R' G G' L L' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hR : R' = R) (hG : G' = G) (hL : L' = L)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ExternalSupplyWitnessUp.mk S' R' G' L' H' C' P' N' =
      ExternalSupplyWitnessUp.mk S R G L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hR
  cases hG
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def externalSupplyWitnessFields : ExternalSupplyWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplyWitnessUp.mk S R G L H C P N => [S, R, G, L, H, C, P, N]

def externalSupplyWitnessToEventFlow : ExternalSupplyWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (externalSupplyWitnessFields x).map externalSupplyWitnessEncodeBHist

private def externalSupplyWitnessRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => externalSupplyWitnessRawAt n rest

private def externalSupplyWitnessLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => externalSupplyWitnessLengthEq n rest

def externalSupplyWitnessFromEventFlow : EventFlow → Option ExternalSupplyWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match externalSupplyWitnessLengthEq 8 flow with
      | true =>
          some
            (ExternalSupplyWitnessUp.mk
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 0 flow))
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 1 flow))
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 2 flow))
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 3 flow))
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 4 flow))
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 5 flow))
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 6 flow))
              (externalSupplyWitnessDecodeBHist (externalSupplyWitnessRawAt 7 flow)))
      | false => none

private theorem ExternalSupplyWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ExternalSupplyWitnessUp,
      externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R G L H C P N =>
      change
        some
          (ExternalSupplyWitnessUp.mk
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist S))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist R))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist G))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist L))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist H))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist C))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist P))
            (externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist N))) =
          some (ExternalSupplyWitnessUp.mk S R G L H C P N)
      exact
        congrArg some
          (externalSupplyWitness_mk_congr
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode S)
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode R)
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode G)
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode L)
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode H)
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode C)
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode P)
            (ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode N))

private theorem ExternalSupplyWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ExternalSupplyWitnessUp} :
    externalSupplyWitnessToEventFlow x = externalSupplyWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) =
        externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow y) :=
    congrArg externalSupplyWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ExternalSupplyWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ExternalSupplyWitnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem ExternalSupplyWitnessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ExternalSupplyWitnessUp, externalSupplyWitnessFields x = externalSupplyWitnessFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ R₁ G₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ G₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance externalSupplyWitnessBHistCarrier : BHistCarrier ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplyWitnessToEventFlow
  fromEventFlow := externalSupplyWitnessFromEventFlow

instance externalSupplyWitnessChapterTasteGate : ChapterTasteGate ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) = some x
    exact ExternalSupplyWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ExternalSupplyWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance externalSupplyWitnessFieldFaithful : FieldFaithful ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := externalSupplyWitnessFields
  field_faithful := ExternalSupplyWitnessTasteGate_single_carrier_alignment_fields_faithful

instance externalSupplyWitnessNontrivial : Nontrivial ExternalSupplyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplyWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplyWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ExternalSupplyWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  externalSupplyWitnessChapterTasteGate

namespace TasteGate

theorem ExternalSupplyWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, externalSupplyWitnessDecodeBHist (externalSupplyWitnessEncodeBHist h) = h) ∧
      (∀ x : ExternalSupplyWitnessUp,
        externalSupplyWitnessFromEventFlow (externalSupplyWitnessToEventFlow x) = some x) ∧
        (∀ x y : ExternalSupplyWitnessUp,
          externalSupplyWitnessToEventFlow x = externalSupplyWitnessToEventFlow y → x = y) ∧
          externalSupplyWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ExternalSupplyWitnessTasteGate_single_carrier_alignment_decode_encode,
      ExternalSupplyWitnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ExternalSupplyWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.ExternalSupplyWitnessUp
