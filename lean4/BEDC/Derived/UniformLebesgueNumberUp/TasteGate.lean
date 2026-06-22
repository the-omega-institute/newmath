import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLebesgueNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLebesgueNumberUp : Type where
  | mk (K M F V L H C P N : BHist) : UniformLebesgueNumberUp
  deriving DecidableEq

def uniformLebesgueNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLebesgueNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLebesgueNumberEncodeBHist h

def uniformLebesgueNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLebesgueNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLebesgueNumberDecodeBHist tail)

private theorem UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLebesgueNumberFields : UniformLebesgueNumberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLebesgueNumberUp.mk K M F V L H C P N => [K, M, F, V, L, H, C, P, N]

def uniformLebesgueNumberToEventFlow : UniformLebesgueNumberUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformLebesgueNumberFields x).map uniformLebesgueNumberEncodeBHist

def uniformLebesgueNumberFromEventFlow : EventFlow → Option UniformLebesgueNumberUp
  -- BEDC touchpoint anchor: BHist BMark
  | [K, M, F, V, L, H, C, P, N] =>
      some
        (UniformLebesgueNumberUp.mk
          (uniformLebesgueNumberDecodeBHist K)
          (uniformLebesgueNumberDecodeBHist M)
          (uniformLebesgueNumberDecodeBHist F)
          (uniformLebesgueNumberDecodeBHist V)
          (uniformLebesgueNumberDecodeBHist L)
          (uniformLebesgueNumberDecodeBHist H)
          (uniformLebesgueNumberDecodeBHist C)
          (uniformLebesgueNumberDecodeBHist P)
          (uniformLebesgueNumberDecodeBHist N))
  | _ => none

private theorem UniformLebesgueNumberTasteGate_single_carrier_alignment_round_trip
    (x : UniformLebesgueNumberUp) :
    uniformLebesgueNumberFromEventFlow (uniformLebesgueNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K M F V L H C P N =>
      change
        some
          (UniformLebesgueNumberUp.mk
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist K))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist M))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist F))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist V))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist L))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist H))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist C))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist P))
            (uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist N))) =
          some (UniformLebesgueNumberUp.mk K M F V L H C P N)
      rw [UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode K,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode M,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode F,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode V,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode L,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode H,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode C,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode P,
        UniformLebesgueNumberTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformLebesgueNumberTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformLebesgueNumberUp} :
    uniformLebesgueNumberToEventFlow x = uniformLebesgueNumberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLebesgueNumberFromEventFlow (uniformLebesgueNumberToEventFlow x) =
        uniformLebesgueNumberFromEventFlow (uniformLebesgueNumberToEventFlow y) :=
    congrArg uniformLebesgueNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformLebesgueNumberTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformLebesgueNumberTasteGate_single_carrier_alignment_round_trip y)))

private theorem uniformLebesgueNumberFields_faithful :
    ∀ x y : UniformLebesgueNumberUp, uniformLebesgueNumberFields x =
      uniformLebesgueNumberFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 M1 F1 V1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 M2 F2 V2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformLebesgueNumberBHistCarrier : BHistCarrier UniformLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLebesgueNumberToEventFlow
  fromEventFlow := uniformLebesgueNumberFromEventFlow

instance uniformLebesgueNumberChapterTasteGate :
    ChapterTasteGate UniformLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLebesgueNumberFromEventFlow (uniformLebesgueNumberToEventFlow x) = some x
    exact UniformLebesgueNumberTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformLebesgueNumberTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformLebesgueNumberFieldFaithful : FieldFaithful UniformLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLebesgueNumberFields
  field_faithful := uniformLebesgueNumberFields_faithful

instance uniformLebesgueNumberNontrivial : Nontrivial UniformLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLebesgueNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLebesgueNumberUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformLebesgueNumberTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformLebesgueNumberDecodeBHist (uniformLebesgueNumberEncodeBHist h) = h) ∧
      uniformLebesgueNumberEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ K M F V L H C P N : BHist,
          uniformLebesgueNumberFields (UniformLebesgueNumberUp.mk K M F V L H C P N) =
            [K, M, F, V, L, H, C, P, N]) ∧
          (∀ x y : UniformLebesgueNumberUp, uniformLebesgueNumberFields x =
            uniformLebesgueNumberFields y → x = y) ∧
            (∃ x y : UniformLebesgueNumberUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · rfl
    · constructor
      · intro K M F V L H C P N
        rfl
      · constructor
        · intro x y hfields
          cases x with
          | mk K1 M1 F1 V1 L1 H1 C1 P1 N1 =>
              cases y with
              | mk K2 M2 F2 V2 L2 H2 C2 P2 N2 =>
                  cases hfields
                  rfl
        · exact
            ⟨UniformLebesgueNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              UniformLebesgueNumberUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩

end BEDC.Derived.UniformLebesgueNumberUp
