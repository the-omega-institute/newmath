import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyApproximationSystemUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyApproximationSystemUp : Type where
  | mk (S W A R M P N : BHist) : CauchyApproximationSystemUp
  deriving DecidableEq

def cauchyApproximationSystemEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyApproximationSystemEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyApproximationSystemEncodeBHist h

def cauchyApproximationSystemDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyApproximationSystemDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyApproximationSystemDecodeBHist tail)

private theorem cauchyApproximationSystemDecode_encode_bhist :
    ∀ h : BHist,
      cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyApproximationSystem_mk_congr
    {S S' W W' A A' R R' M M' P P' N N' : BHist}
    (hS : S' = S)
    (hW : W' = W)
    (hA : A' = A)
    (hR : R' = R)
    (hM : M' = M)
    (hP : P' = P)
    (hN : N' = N) :
    CauchyApproximationSystemUp.mk S' W' A' R' M' P' N' =
      CauchyApproximationSystemUp.mk S W A R M P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hW
  cases hA
  cases hR
  cases hM
  cases hP
  cases hN
  rfl

def cauchyApproximationSystemFields : CauchyApproximationSystemUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyApproximationSystemUp.mk S W A R M P N => [S, W, A, R, M, P, N]

def cauchyApproximationSystemToEventFlow : CauchyApproximationSystemUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyApproximationSystemUp.mk S W A R M P N =>
      [cauchyApproximationSystemEncodeBHist S,
        cauchyApproximationSystemEncodeBHist W,
        cauchyApproximationSystemEncodeBHist A,
        cauchyApproximationSystemEncodeBHist R,
        cauchyApproximationSystemEncodeBHist M,
        cauchyApproximationSystemEncodeBHist P,
        cauchyApproximationSystemEncodeBHist N]

private def cauchyApproximationSystemEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyApproximationSystemEventAtDefault index rest

def cauchyApproximationSystemFromEventFlow
    (ef : EventFlow) : Option CauchyApproximationSystemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyApproximationSystemUp.mk
      (cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEventAtDefault 0 ef))
      (cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEventAtDefault 1 ef))
      (cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEventAtDefault 2 ef))
      (cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEventAtDefault 3 ef))
      (cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEventAtDefault 4 ef))
      (cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEventAtDefault 5 ef))
      (cauchyApproximationSystemDecodeBHist
        (cauchyApproximationSystemEventAtDefault 6 ef)))

private theorem cauchyApproximationSystem_round_trip :
    ∀ x : CauchyApproximationSystemUp,
      cauchyApproximationSystemFromEventFlow
        (cauchyApproximationSystemToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W A R M P N =>
      exact
        congrArg some
          (cauchyApproximationSystem_mk_congr
            (cauchyApproximationSystemDecode_encode_bhist S)
            (cauchyApproximationSystemDecode_encode_bhist W)
            (cauchyApproximationSystemDecode_encode_bhist A)
            (cauchyApproximationSystemDecode_encode_bhist R)
            (cauchyApproximationSystemDecode_encode_bhist M)
            (cauchyApproximationSystemDecode_encode_bhist P)
            (cauchyApproximationSystemDecode_encode_bhist N))

private theorem cauchyApproximationSystemToEventFlow_injective
    {x y : CauchyApproximationSystemUp} :
    cauchyApproximationSystemToEventFlow x =
      cauchyApproximationSystemToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyApproximationSystemFromEventFlow
          (cauchyApproximationSystemToEventFlow x) =
        cauchyApproximationSystemFromEventFlow
          (cauchyApproximationSystemToEventFlow y) :=
    congrArg cauchyApproximationSystemFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyApproximationSystem_round_trip x).symm
      (Eq.trans hread (cauchyApproximationSystem_round_trip y)))

private theorem cauchyApproximationSystem_fields_faithful :
    ∀ x y : CauchyApproximationSystemUp,
      cauchyApproximationSystemFields x =
        cauchyApproximationSystemFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ W₁ A₁ R₁ M₁ P₁ N₁ =>
      cases y with
      | mk S₂ W₂ A₂ R₂ M₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyApproximationSystemBHistCarrier :
    BHistCarrier CauchyApproximationSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyApproximationSystemToEventFlow
  fromEventFlow := cauchyApproximationSystemFromEventFlow

instance cauchyApproximationSystemChapterTasteGate :
    ChapterTasteGate CauchyApproximationSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyApproximationSystemFromEventFlow
        (cauchyApproximationSystemToEventFlow x) = some x
    exact cauchyApproximationSystem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyApproximationSystemToEventFlow_injective heq)

instance cauchyApproximationSystemFieldFaithful :
    FieldFaithful CauchyApproximationSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyApproximationSystemFields
  field_faithful := cauchyApproximationSystem_fields_faithful

def taste_gate : ChapterTasteGate CauchyApproximationSystemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyApproximationSystemChapterTasteGate

theorem CauchyApproximationSystemUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyApproximationSystemUp) ∧
      Nonempty (FieldFaithful CauchyApproximationSystemUp) ∧
        (∀ h : BHist,
          cauchyApproximationSystemDecodeBHist
            (cauchyApproximationSystemEncodeBHist h) = h) ∧
          cauchyApproximationSystemEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark RawEvent FieldFaithful ChapterTasteGate
  constructor
  · exact ⟨cauchyApproximationSystemChapterTasteGate⟩
  · constructor
    · exact ⟨cauchyApproximationSystemFieldFaithful⟩
    · constructor
      · exact cauchyApproximationSystemDecode_encode_bhist
      · rfl

end BEDC.Derived.CauchyApproximationSystemUp
