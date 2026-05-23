import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatorUp : Type where
  | mk (D U I L R B Q P N : BHist) : RegulatorUp
  deriving DecidableEq

def RegulatorTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RegulatorTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RegulatorTasteGate_single_carrier_alignment_encodeBHist h

def RegulatorTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (RegulatorTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (RegulatorTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegulatorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RegulatorTasteGate_single_carrier_alignment_decodeBHist
          (RegulatorTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def RegulatorTasteGate_single_carrier_alignment_fields :
    RegulatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatorUp.mk D U I L R B Q P N => [D, U, I, L, R, B, Q, P, N]

def RegulatorTasteGate_single_carrier_alignment_toEventFlow :
    RegulatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RegulatorTasteGate_single_carrier_alignment_fields x).map
      RegulatorTasteGate_single_carrier_alignment_encodeBHist

def RegulatorTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegulatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | D :: U :: I :: L :: R :: B :: Q :: P :: N :: [] =>
      some
        (RegulatorUp.mk
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist D)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist U)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist I)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist L)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist R)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist B)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist Q)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist P)
          (RegulatorTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem RegulatorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegulatorUp,
      RegulatorTasteGate_single_carrier_alignment_fromEventFlow
          (RegulatorTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk D U I L R B Q P N =>
      simp only [RegulatorTasteGate_single_carrier_alignment_toEventFlow,
        RegulatorTasteGate_single_carrier_alignment_fields,
        RegulatorTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons, List.map_nil,
        RegulatorTasteGate_single_carrier_alignment_decode_encode]

private theorem RegulatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatorUp} :
    RegulatorTasteGate_single_carrier_alignment_toEventFlow x =
        RegulatorTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          RegulatorTasteGate_single_carrier_alignment_fromEventFlow
            (RegulatorTasteGate_single_carrier_alignment_toEventFlow x) :=
        (RegulatorTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          RegulatorTasteGate_single_carrier_alignment_fromEventFlow
            (RegulatorTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg RegulatorTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := RegulatorTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem RegulatorTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegulatorUp,
      RegulatorTasteGate_single_carrier_alignment_fields x =
          RegulatorTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ U₁ I₁ L₁ R₁ B₁ Q₁ P₁ N₁ =>
      cases y with
      | mk D₂ U₂ I₂ L₂ R₂ B₂ Q₂ P₂ N₂ =>
          cases hfields
          rfl

instance RegulatorTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RegulatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegulatorTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegulatorTasteGate_single_carrier_alignment_fromEventFlow

instance RegulatorTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RegulatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegulatorTasteGate_single_carrier_alignment_fromEventFlow
          (RegulatorTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RegulatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RegulatorTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RegulatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegulatorTasteGate_single_carrier_alignment_fields
  field_faithful := RegulatorTasteGate_single_carrier_alignment_field_faithful

instance RegulatorTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial RegulatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegulatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegulatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegulatorTasteGate_single_carrier_alignment :
    (forall D U I L R B Q P N : BHist,
      RegulatorTasteGate_single_carrier_alignment_fields
          (RegulatorUp.mk D U I L R B Q P N) =
        [D, U, I, L, R, B, Q, P, N]) ∧
      RegulatorTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨(fun _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.RegulatorUp
