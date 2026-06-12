import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HadamardThreeCircleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HadamardThreeCircleUp : Type where
  | mk (A F R0 R1 R2 B M L H C P N : BHist) : HadamardThreeCircleUp
  deriving DecidableEq

def hadamardThreeCircleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hadamardThreeCircleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hadamardThreeCircleEncodeBHist h

def hadamardThreeCircleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hadamardThreeCircleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hadamardThreeCircleDecodeBHist tail)

private theorem HadamardThreeCircleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hadamardThreeCircleFields : HadamardThreeCircleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HadamardThreeCircleUp.mk A F R0 R1 R2 B M L H C P N =>
      [A, F, R0, R1, R2, B, M, L, H, C, P, N]

def hadamardThreeCircleToEventFlow : HadamardThreeCircleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hadamardThreeCircleFields x).map hadamardThreeCircleEncodeBHist

private def hadamardThreeCircleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hadamardThreeCircleEventAtDefault index rest

def hadamardThreeCircleFromEventFlow (ef : EventFlow) : Option HadamardThreeCircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HadamardThreeCircleUp.mk
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 0 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 1 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 2 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 3 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 4 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 5 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 6 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 7 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 8 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 9 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 10 ef))
      (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEventAtDefault 11 ef)))

private theorem HadamardThreeCircleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HadamardThreeCircleUp,
      hadamardThreeCircleFromEventFlow (hadamardThreeCircleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A F R0 R1 R2 B M L H C P N =>
      change
        some
          (HadamardThreeCircleUp.mk
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist A))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist F))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist R0))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist R1))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist R2))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist B))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist M))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist L))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist H))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist C))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist P))
            (hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist N))) =
          some (HadamardThreeCircleUp.mk A F R0 R1 R2 B M L H C P N)
      rw [HadamardThreeCircleTasteGate_single_carrier_alignment_decode A,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode F,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode R0,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode R1,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode R2,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode B,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode M,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode L,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode H,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode C,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode P,
        HadamardThreeCircleTasteGate_single_carrier_alignment_decode N]

private theorem HadamardThreeCircleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HadamardThreeCircleUp} :
    hadamardThreeCircleToEventFlow x = hadamardThreeCircleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hadamardThreeCircleFromEventFlow (hadamardThreeCircleToEventFlow x) =
        hadamardThreeCircleFromEventFlow (hadamardThreeCircleToEventFlow y) :=
    congrArg hadamardThreeCircleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HadamardThreeCircleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HadamardThreeCircleTasteGate_single_carrier_alignment_round_trip y)))

private theorem HadamardThreeCircleTasteGate_single_carrier_alignment_fields :
    ∀ x y : HadamardThreeCircleUp,
      hadamardThreeCircleFields x = hadamardThreeCircleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 F1 R01 R11 R21 B1 M1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 F2 R02 R12 R22 B2 M2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hadamardThreeCircleBHistCarrier : BHistCarrier HadamardThreeCircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hadamardThreeCircleToEventFlow
  fromEventFlow := hadamardThreeCircleFromEventFlow

instance hadamardThreeCircleChapterTasteGate : ChapterTasteGate HadamardThreeCircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hadamardThreeCircleFromEventFlow (hadamardThreeCircleToEventFlow x) = some x
    exact HadamardThreeCircleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HadamardThreeCircleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hadamardThreeCircleFieldFaithful : FieldFaithful HadamardThreeCircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hadamardThreeCircleFields
  field_faithful := HadamardThreeCircleTasteGate_single_carrier_alignment_fields

instance hadamardThreeCircleNontrivial : BEDC.Meta.TasteGate.Nontrivial HadamardThreeCircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HadamardThreeCircleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HadamardThreeCircleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HadamardThreeCircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hadamardThreeCircleChapterTasteGate

theorem HadamardThreeCircleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HadamardThreeCircleUp) ∧
      Nonempty (FieldFaithful HadamardThreeCircleUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HadamardThreeCircleUp) ∧
          (∀ h : BHist,
            hadamardThreeCircleDecodeBHist (hadamardThreeCircleEncodeBHist h) = h) ∧
            (∀ x : HadamardThreeCircleUp,
              hadamardThreeCircleFromEventFlow (hadamardThreeCircleToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨hadamardThreeCircleChapterTasteGate⟩,
      ⟨hadamardThreeCircleFieldFaithful⟩,
      ⟨hadamardThreeCircleNontrivial⟩,
      HadamardThreeCircleTasteGate_single_carrier_alignment_decode,
      HadamardThreeCircleTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.HadamardThreeCircleUp
