import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClassifyingSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClassifyingSpaceUp : Type where
  | mk (G U S H C T R P N : BHist) : ClassifyingSpaceUp
  deriving DecidableEq

def classifyingSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: classifyingSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: classifyingSpaceEncodeBHist h

def classifyingSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (classifyingSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (classifyingSpaceDecodeBHist tail)

private theorem ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def classifyingSpaceToEventFlow : ClassifyingSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClassifyingSpaceUp.mk G U S H C T R P N =>
      [classifyingSpaceEncodeBHist G,
        classifyingSpaceEncodeBHist U,
        classifyingSpaceEncodeBHist S,
        classifyingSpaceEncodeBHist H,
        classifyingSpaceEncodeBHist C,
        classifyingSpaceEncodeBHist T,
        classifyingSpaceEncodeBHist R,
        classifyingSpaceEncodeBHist P,
        classifyingSpaceEncodeBHist N]

private def classifyingSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => classifyingSpaceEventAtDefault index rest

def classifyingSpaceFromEventFlow (ef : EventFlow) : Option ClassifyingSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClassifyingSpaceUp.mk
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 0 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 1 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 2 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 3 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 4 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 5 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 6 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 7 ef))
      (classifyingSpaceDecodeBHist (classifyingSpaceEventAtDefault 8 ef)))

private theorem ClassifyingSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClassifyingSpaceUp,
      classifyingSpaceFromEventFlow (classifyingSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G U S H C T R P N =>
      change
        some
          (ClassifyingSpaceUp.mk
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist G))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist U))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist S))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist H))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist C))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist T))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist R))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist P))
            (classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist N))) =
          some (ClassifyingSpaceUp.mk G U S H C T R P N)
      rw [ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode G,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode U,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode S,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode H,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode C,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode T,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode R,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode P,
        ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem ClassifyingSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClassifyingSpaceUp} :
    classifyingSpaceToEventFlow x = classifyingSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      classifyingSpaceFromEventFlow (classifyingSpaceToEventFlow x) =
        classifyingSpaceFromEventFlow (classifyingSpaceToEventFlow y) :=
    congrArg classifyingSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClassifyingSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClassifyingSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance classifyingSpaceBHistCarrier : BHistCarrier ClassifyingSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := classifyingSpaceToEventFlow
  fromEventFlow := classifyingSpaceFromEventFlow

instance classifyingSpaceChapterTasteGate : ChapterTasteGate ClassifyingSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change classifyingSpaceFromEventFlow (classifyingSpaceToEventFlow x) = some x
    exact ClassifyingSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClassifyingSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance classifyingSpaceFieldFaithful : FieldFaithful ClassifyingSpaceUp where
  fields := fun x =>
    match x with
    | ClassifyingSpaceUp.mk G U S H C T R P N => [G, U, S, H, C, T, R, P, N]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk G1 U1 S1 H1 C1 T1 R1 P1 N1 =>
      cases y with
      | mk G2 U2 S2 H2 C2 T2 R2 P2 N2 =>
        cases h
        rfl

instance classifyingSpaceNontrivial : Nontrivial ClassifyingSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClassifyingSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClassifyingSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def classifyingSpaceTasteGate : ChapterTasteGate ClassifyingSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  classifyingSpaceChapterTasteGate

theorem ClassifyingSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, classifyingSpaceDecodeBHist (classifyingSpaceEncodeBHist h) = h) ∧
      (∀ x : ClassifyingSpaceUp,
        classifyingSpaceFromEventFlow (classifyingSpaceToEventFlow x) = some x) ∧
        (∀ x y : ClassifyingSpaceUp,
          classifyingSpaceToEventFlow x = classifyingSpaceToEventFlow y → x = y) ∧
          classifyingSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ClassifyingSpaceTasteGate_single_carrier_alignment_decode_encode,
      ClassifyingSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ClassifyingSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ClassifyingSpaceUp
