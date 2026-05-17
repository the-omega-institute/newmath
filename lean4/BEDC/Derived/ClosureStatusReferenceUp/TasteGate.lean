import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosureStatusReferenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosureStatusReferenceUp : Type where
  | mk : (S T F L B N U H C P Q : BHist) → ClosureStatusReferenceUp
  deriving DecidableEq

def closureStatusReferenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closureStatusReferenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closureStatusReferenceEncodeBHist h

def closureStatusReferenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closureStatusReferenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closureStatusReferenceDecodeBHist tail)

private theorem closureStatusReferenceDecode_encode_bhist :
    ∀ h : BHist, closureStatusReferenceDecodeBHist
      (closureStatusReferenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closureStatusReferenceFields : ClosureStatusReferenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosureStatusReferenceUp.mk S T F L B N U H C P Q => [S, T, F, L, B, N, U, H, C, P, Q]

def closureStatusReferenceToEventFlow : ClosureStatusReferenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closureStatusReferenceFields x).map closureStatusReferenceEncodeBHist

def closureStatusReferenceFromEventFlow : EventFlow → Option ClosureStatusReferenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, T, F, L, B, N, U, H, C, P, Q] =>
      some
        (ClosureStatusReferenceUp.mk
          (closureStatusReferenceDecodeBHist S)
          (closureStatusReferenceDecodeBHist T)
          (closureStatusReferenceDecodeBHist F)
          (closureStatusReferenceDecodeBHist L)
          (closureStatusReferenceDecodeBHist B)
          (closureStatusReferenceDecodeBHist N)
          (closureStatusReferenceDecodeBHist U)
          (closureStatusReferenceDecodeBHist H)
          (closureStatusReferenceDecodeBHist C)
          (closureStatusReferenceDecodeBHist P)
          (closureStatusReferenceDecodeBHist Q))
  | _ => none

private theorem closureStatusReference_round_trip :
    ∀ x : ClosureStatusReferenceUp,
      closureStatusReferenceFromEventFlow
        (closureStatusReferenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T F L B N U H C P Q =>
      change
        some
          (ClosureStatusReferenceUp.mk
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist S))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist T))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist F))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist L))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist B))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist N))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist U))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist H))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist C))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist P))
            (closureStatusReferenceDecodeBHist (closureStatusReferenceEncodeBHist Q))) =
          some (ClosureStatusReferenceUp.mk S T F L B N U H C P Q)
      rw [closureStatusReferenceDecode_encode_bhist S,
        closureStatusReferenceDecode_encode_bhist T,
        closureStatusReferenceDecode_encode_bhist F,
        closureStatusReferenceDecode_encode_bhist L,
        closureStatusReferenceDecode_encode_bhist B,
        closureStatusReferenceDecode_encode_bhist N,
        closureStatusReferenceDecode_encode_bhist U,
        closureStatusReferenceDecode_encode_bhist H,
        closureStatusReferenceDecode_encode_bhist C,
        closureStatusReferenceDecode_encode_bhist P,
        closureStatusReferenceDecode_encode_bhist Q]

private theorem closureStatusReferenceToEventFlow_injective {x y : ClosureStatusReferenceUp} :
    closureStatusReferenceToEventFlow x =
      closureStatusReferenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closureStatusReferenceFromEventFlow
          (closureStatusReferenceToEventFlow x) =
        closureStatusReferenceFromEventFlow
          (closureStatusReferenceToEventFlow y) :=
    congrArg closureStatusReferenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closureStatusReference_round_trip x).symm
      (Eq.trans hread (closureStatusReference_round_trip y)))

instance closureStatusReferenceBHistCarrier :
    BHistCarrier ClosureStatusReferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closureStatusReferenceToEventFlow
  fromEventFlow := closureStatusReferenceFromEventFlow

instance closureStatusReferenceChapterTasteGate :
    ChapterTasteGate ClosureStatusReferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closureStatusReferenceFromEventFlow
        (closureStatusReferenceToEventFlow x) = some x
    exact closureStatusReference_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closureStatusReferenceToEventFlow_injective heq)

instance closureStatusReferenceFieldFaithful :
    FieldFaithful ClosureStatusReferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closureStatusReferenceFields
  field_faithful := by
    intro x y h
    cases x with
    | mk S₁ T₁ F₁ L₁ B₁ N₁ U₁ H₁ C₁ P₁ Q₁ =>
        cases y with
        | mk S₂ T₂ F₂ L₂ B₂ N₂ U₂ H₂ C₂ P₂ Q₂ =>
            injection h with hS hRest₁
            injection hRest₁ with hT hRest₂
            injection hRest₂ with hF hRest₃
            injection hRest₃ with hL hRest₄
            injection hRest₄ with hB hRest₅
            injection hRest₅ with hN hRest₆
            injection hRest₆ with hU hRest₇
            injection hRest₇ with hH hRest₈
            injection hRest₈ with hC hRest₉
            injection hRest₉ with hP hRest₁₀
            injection hRest₁₀ with hQ _
            subst hS
            subst hT
            subst hF
            subst hL
            subst hB
            subst hN
            subst hU
            subst hH
            subst hC
            subst hP
            subst hQ
            rfl

instance closureStatusReferenceNontrivial :
    Nontrivial ClosureStatusReferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosureStatusReferenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosureStatusReferenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ClosureStatusReferenceTasteGate_single_carrier_alignment :
    ∀ x : ClosureStatusReferenceUp,
      ∃ S T F L B N U H C P Q : BHist,
        x = ClosureStatusReferenceUp.mk S T F L B N U H C P Q := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  intro x
  cases x with
  | mk S T F L B N U H C P Q =>
      exact ⟨S, T, F, L, B, N, U, H, C, P, Q, rfl⟩

end BEDC.Derived.ClosureStatusReferenceUp
