import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleeneTreeBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleeneTreeBoundaryUp : Type where
  | mk (K F S R E O H C P N : BHist) : KleeneTreeBoundaryUp
  deriving DecidableEq

def kleeneTreeBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kleeneTreeBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kleeneTreeBoundaryEncodeBHist h

def kleeneTreeBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kleeneTreeBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kleeneTreeBoundaryDecodeBHist tail)

private theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kleeneTreeBoundaryToEventFlow : KleeneTreeBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KleeneTreeBoundaryUp.mk K F S R E O H C P N =>
      [[BMark.b0],
        kleeneTreeBoundaryEncodeBHist K,
        [BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kleeneTreeBoundaryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        kleeneTreeBoundaryEncodeBHist N]

def kleeneTreeBoundaryFromEventFlow : EventFlow → Option KleeneTreeBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b0], K, [BMark.b1, BMark.b0], F, [BMark.b1, BMark.b1, BMark.b0], S,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b0], R,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], E,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], O,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], H,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b0], C,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b0], P,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b1, BMark.b0], N] =>
      some
        (KleeneTreeBoundaryUp.mk
          (kleeneTreeBoundaryDecodeBHist K)
          (kleeneTreeBoundaryDecodeBHist F)
          (kleeneTreeBoundaryDecodeBHist S)
          (kleeneTreeBoundaryDecodeBHist R)
          (kleeneTreeBoundaryDecodeBHist E)
          (kleeneTreeBoundaryDecodeBHist O)
          (kleeneTreeBoundaryDecodeBHist H)
          (kleeneTreeBoundaryDecodeBHist C)
          (kleeneTreeBoundaryDecodeBHist P)
          (kleeneTreeBoundaryDecodeBHist N))
  | _ => none

private theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KleeneTreeBoundaryUp,
      kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F S R E O H C P N =>
      change
        some
          (KleeneTreeBoundaryUp.mk
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist K))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist F))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist S))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist R))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist E))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist O))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist H))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist C))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist P))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist N))) =
          some (KleeneTreeBoundaryUp.mk K F S R E O H C P N)
      rw [KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode K,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode F,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode S,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode R,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode E,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode O,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode H,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode C,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode P,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment_injective
    {x y : KleeneTreeBoundaryUp} :
    kleeneTreeBoundaryToEventFlow x = kleeneTreeBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) =
        kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow y) :=
    congrArg kleeneTreeBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KleeneTreeBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KleeneTreeBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private def kleeneTreeBoundaryFields : KleeneTreeBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleeneTreeBoundaryUp.mk K F S R E O H C P N => [K, F, S, R, E, O, H, C, P, N]

private theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment_fields :
    ∀ x y : KleeneTreeBoundaryUp, kleeneTreeBoundaryFields x = kleeneTreeBoundaryFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 S1 R1 E1 O1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 S2 R2 E2 O2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance kleeneTreeBoundaryBHistCarrier : BHistCarrier KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kleeneTreeBoundaryToEventFlow
  fromEventFlow := kleeneTreeBoundaryFromEventFlow

instance kleeneTreeBoundaryChapterTasteGate : ChapterTasteGate KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) = some x
    exact KleeneTreeBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KleeneTreeBoundaryTasteGate_single_carrier_alignment_injective heq)

instance kleeneTreeBoundaryFieldFaithful : FieldFaithful KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kleeneTreeBoundaryFields
  field_faithful := KleeneTreeBoundaryTasteGate_single_carrier_alignment_fields

instance kleeneTreeBoundaryNontrivial : Nontrivial KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KleeneTreeBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KleeneTreeBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist h) = h) ∧
      (∀ x : KleeneTreeBoundaryUp,
        kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) = some x) ∧
        (∀ x y : KleeneTreeBoundaryUp,
          kleeneTreeBoundaryToEventFlow x = kleeneTreeBoundaryToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate KleeneTreeBoundaryUp) ∧
            Nonempty (FieldFaithful KleeneTreeBoundaryUp) ∧
              Nonempty (Nontrivial KleeneTreeBoundaryUp) ∧
                kleeneTreeBoundaryEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode
  constructor
  · exact KleeneTreeBoundaryTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact KleeneTreeBoundaryTasteGate_single_carrier_alignment_injective heq
  constructor
  · exact ⟨kleeneTreeBoundaryChapterTasteGate⟩
  constructor
  · exact ⟨kleeneTreeBoundaryFieldFaithful⟩
  constructor
  · exact ⟨kleeneTreeBoundaryNontrivial⟩
  · rfl

end BEDC.Derived.KleeneTreeBoundaryUp.TasteGate
