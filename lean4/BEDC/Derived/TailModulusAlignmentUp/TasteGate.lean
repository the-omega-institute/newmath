import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailModulusAlignmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailModulusAlignmentUp : Type where
  | mk (refinement schedule fusion windows readback dyadic sealRow transport route provenance
      name : BHist) : TailModulusAlignmentUp
  deriving DecidableEq

def tailModulusAlignmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailModulusAlignmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailModulusAlignmentEncodeBHist h

def tailModulusAlignmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailModulusAlignmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailModulusAlignmentDecodeBHist tail)

private theorem tailModulusAlignmentDecode_encode_bhist :
    ∀ h : BHist, tailModulusAlignmentDecodeBHist
      (tailModulusAlignmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tailModulusAlignmentToEventFlow : TailModulusAlignmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TailModulusAlignmentUp.mk refinement schedule fusion windows readback dyadic sealRow
      transport route provenance name =>
      [tailModulusAlignmentEncodeBHist refinement,
        tailModulusAlignmentEncodeBHist schedule,
        tailModulusAlignmentEncodeBHist fusion,
        tailModulusAlignmentEncodeBHist windows,
        tailModulusAlignmentEncodeBHist readback,
        tailModulusAlignmentEncodeBHist dyadic,
        tailModulusAlignmentEncodeBHist sealRow,
        tailModulusAlignmentEncodeBHist transport,
        tailModulusAlignmentEncodeBHist route,
        tailModulusAlignmentEncodeBHist provenance,
        tailModulusAlignmentEncodeBHist name]

private def tailModulusAlignmentEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tailModulusAlignmentEventAtDefault index rest

def tailModulusAlignmentFromEventFlow (ef : EventFlow) : Option TailModulusAlignmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TailModulusAlignmentUp.mk
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 0 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 1 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 2 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 3 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 4 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 5 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 6 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 7 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 8 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 9 ef))
      (tailModulusAlignmentDecodeBHist (tailModulusAlignmentEventAtDefault 10 ef)))

private theorem tailModulusAlignment_round_trip :
    ∀ x : TailModulusAlignmentUp,
      tailModulusAlignmentFromEventFlow (tailModulusAlignmentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk refinement schedule fusion windows readback dyadic sealRow transport route provenance name =>
      change
        some
          (TailModulusAlignmentUp.mk
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist refinement))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist schedule))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist fusion))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist windows))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist readback))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist dyadic))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist sealRow))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist transport))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist route))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist provenance))
            (tailModulusAlignmentDecodeBHist
              (tailModulusAlignmentEncodeBHist name))) =
          some
            (TailModulusAlignmentUp.mk refinement schedule fusion windows readback dyadic
              sealRow transport route provenance name)
      rw [tailModulusAlignmentDecode_encode_bhist refinement,
        tailModulusAlignmentDecode_encode_bhist schedule,
        tailModulusAlignmentDecode_encode_bhist fusion,
        tailModulusAlignmentDecode_encode_bhist windows,
        tailModulusAlignmentDecode_encode_bhist readback,
        tailModulusAlignmentDecode_encode_bhist dyadic,
        tailModulusAlignmentDecode_encode_bhist sealRow,
        tailModulusAlignmentDecode_encode_bhist transport,
        tailModulusAlignmentDecode_encode_bhist route,
        tailModulusAlignmentDecode_encode_bhist provenance,
        tailModulusAlignmentDecode_encode_bhist name]

private theorem tailModulusAlignmentToEventFlow_injective
    {x y : TailModulusAlignmentUp} :
    tailModulusAlignmentToEventFlow x = tailModulusAlignmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tailModulusAlignmentFromEventFlow (tailModulusAlignmentToEventFlow x) =
        tailModulusAlignmentFromEventFlow (tailModulusAlignmentToEventFlow y) :=
    congrArg tailModulusAlignmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tailModulusAlignment_round_trip x).symm
      (Eq.trans hread (tailModulusAlignment_round_trip y)))

instance tailModulusAlignmentBHistCarrier : BHistCarrier TailModulusAlignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailModulusAlignmentToEventFlow
  fromEventFlow := tailModulusAlignmentFromEventFlow

instance tailModulusAlignmentChapterTasteGate : ChapterTasteGate TailModulusAlignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tailModulusAlignmentFromEventFlow (tailModulusAlignmentToEventFlow x) = some x
    exact tailModulusAlignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tailModulusAlignmentToEventFlow_injective heq)

instance tailModulusAlignmentFieldFaithful : FieldFaithful TailModulusAlignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TailModulusAlignmentUp.mk refinement schedule fusion windows readback dyadic sealRow
        transport route provenance name =>
        [refinement, schedule, fusion, windows, readback, dyadic, sealRow, transport, route,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk refinement₁ schedule₁ fusion₁ windows₁ readback₁ dyadic₁ sealRow₁ transport₁ route₁
        provenance₁ name₁ =>
        cases y with
        | mk refinement₂ schedule₂ fusion₂ windows₂ readback₂ dyadic₂ sealRow₂ transport₂
            route₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance tailModulusAlignmentNontrivial : Nontrivial TailModulusAlignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TailModulusAlignmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TailModulusAlignmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def tail_modulus_alignment_taste_gate : ChapterTasteGate TailModulusAlignmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tailModulusAlignmentChapterTasteGate

namespace TasteGate

theorem TailModulusAlignmentTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        tailModulusAlignmentDecodeBHist (tailModulusAlignmentEncodeBHist h) = h) ∧
      (∀ x : TailModulusAlignmentUp,
        tailModulusAlignmentFromEventFlow (tailModulusAlignmentToEventFlow x) = some x) ∧
      (∀ x y : TailModulusAlignmentUp,
        tailModulusAlignmentToEventFlow x = tailModulusAlignmentToEventFlow y → x = y) ∧
      tailModulusAlignmentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact tailModulusAlignmentDecode_encode_bhist
  · constructor
    · exact tailModulusAlignment_round_trip
    · constructor
      · intro x y heq
        exact tailModulusAlignmentToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.TailModulusAlignmentUp
