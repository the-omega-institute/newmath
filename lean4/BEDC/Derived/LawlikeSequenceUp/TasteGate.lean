import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LawlikeSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LawlikeSequenceUp : Type where
  | mk (R W O H C P N : BHist) : LawlikeSequenceUp
  deriving DecidableEq

def lawlikeSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawlikeSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawlikeSequenceEncodeBHist h

def lawlikeSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawlikeSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawlikeSequenceDecodeBHist tail)

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective
    {a b : BHist} :
    lawlikeSequenceEncodeBHist a = lawlikeSequenceEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  have hd :
      lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist a) =
        lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist b) :=
    congrArg lawlikeSequenceDecodeBHist h
  exact Eq.trans
    (LawlikeSequenceTasteGate_single_carrier_alignment_decode a).symm
    (Eq.trans hd (LawlikeSequenceTasteGate_single_carrier_alignment_decode b))

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_mk_congr
    {R R' W W' O O' H H' C C' P P' N N' : BHist}
    (hR : R' = R)
    (hW : W' = W)
    (hO : O' = O)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    LawlikeSequenceUp.mk R' W' O' H' C' P' N' = LawlikeSequenceUp.mk R W O H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hW
  cases hO
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def LawlikeSequenceTasteGate_single_carrier_alignment_rawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => LawlikeSequenceTasteGate_single_carrier_alignment_rawAt n rest

def lawlikeSequenceFields : LawlikeSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LawlikeSequenceUp.mk R W O H C P N => [R, W, O, H, C, P, N]

def lawlikeSequenceToEventFlow : LawlikeSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LawlikeSequenceUp.mk R W O H C P N =>
      [lawlikeSequenceEncodeBHist R, lawlikeSequenceEncodeBHist W,
        lawlikeSequenceEncodeBHist O, lawlikeSequenceEncodeBHist H,
        lawlikeSequenceEncodeBHist C, lawlikeSequenceEncodeBHist P,
        lawlikeSequenceEncodeBHist N]

def lawlikeSequenceFromEventFlow : EventFlow → Option LawlikeSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LawlikeSequenceUp.mk
          (lawlikeSequenceDecodeBHist
            (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 0 ef))
          (lawlikeSequenceDecodeBHist
            (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 1 ef))
          (lawlikeSequenceDecodeBHist
            (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 2 ef))
          (lawlikeSequenceDecodeBHist
            (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 3 ef))
          (lawlikeSequenceDecodeBHist
            (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 4 ef))
          (lawlikeSequenceDecodeBHist
            (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 5 ef))
          (lawlikeSequenceDecodeBHist
            (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 6 ef)))

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LawlikeSequenceUp,
      lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W O H C P N =>
      exact
        congrArg some
          (LawlikeSequenceTasteGate_single_carrier_alignment_mk_congr
            (LawlikeSequenceTasteGate_single_carrier_alignment_decode R)
            (LawlikeSequenceTasteGate_single_carrier_alignment_decode W)
            (LawlikeSequenceTasteGate_single_carrier_alignment_decode O)
            (LawlikeSequenceTasteGate_single_carrier_alignment_decode H)
            (LawlikeSequenceTasteGate_single_carrier_alignment_decode C)
            (LawlikeSequenceTasteGate_single_carrier_alignment_decode P)
            (LawlikeSequenceTasteGate_single_carrier_alignment_decode N))

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LawlikeSequenceUp} :
    lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk R₁ W₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ W₂ O₂ H₂ C₂ P₂ N₂ =>
          have hR :
              lawlikeSequenceEncodeBHist R₁ = lawlikeSequenceEncodeBHist R₂ :=
            congrArg (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 0) heq
          have hW :
              lawlikeSequenceEncodeBHist W₁ = lawlikeSequenceEncodeBHist W₂ :=
            congrArg (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 1) heq
          have hO :
              lawlikeSequenceEncodeBHist O₁ = lawlikeSequenceEncodeBHist O₂ :=
            congrArg (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 2) heq
          have hH :
              lawlikeSequenceEncodeBHist H₁ = lawlikeSequenceEncodeBHist H₂ :=
            congrArg (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 3) heq
          have hC :
              lawlikeSequenceEncodeBHist C₁ = lawlikeSequenceEncodeBHist C₂ :=
            congrArg (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 4) heq
          have hP :
              lawlikeSequenceEncodeBHist P₁ = lawlikeSequenceEncodeBHist P₂ :=
            congrArg (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 5) heq
          have hN :
              lawlikeSequenceEncodeBHist N₁ = lawlikeSequenceEncodeBHist N₂ :=
            congrArg (LawlikeSequenceTasteGate_single_carrier_alignment_rawAt 6) heq
          cases LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective hR
          cases LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective hW
          cases LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective hO
          cases LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective hH
          cases LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective hC
          cases LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective hP
          cases LawlikeSequenceTasteGate_single_carrier_alignment_encode_injective hN
          rfl

private theorem LawlikeSequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : LawlikeSequenceUp, lawlikeSequenceFields x = lawlikeSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ W₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ W₂ O₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lawlikeSequenceBHistCarrier : BHistCarrier LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawlikeSequenceToEventFlow
  fromEventFlow := lawlikeSequenceFromEventFlow

instance lawlikeSequenceChapterTasteGate : ChapterTasteGate LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x
    exact LawlikeSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LawlikeSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lawlikeSequenceFieldFaithful : FieldFaithful LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lawlikeSequenceFields
  field_faithful := LawlikeSequenceTasteGate_single_carrier_alignment_fields

def LawlikeSequenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LawlikeSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawlikeSequenceChapterTasteGate

theorem LawlikeSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h) ∧
      (∀ x : LawlikeSequenceUp,
        lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x) ∧
      (∀ x y : LawlikeSequenceUp,
        lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y) ∧
      lawlikeSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LawlikeSequenceTasteGate_single_carrier_alignment_decode
  constructor
  · exact LawlikeSequenceTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro _ _ heq
    exact LawlikeSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.LawlikeSequenceUp
