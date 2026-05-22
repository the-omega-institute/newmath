import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformHomeomorphismUp : Type where
  | mk (X Y f g F G M N H C P L : BHist) : UniformHomeomorphismUp
  deriving DecidableEq

def uniformHomeomorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformHomeomorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformHomeomorphismEncodeBHist h

def uniformHomeomorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformHomeomorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformHomeomorphismDecodeBHist tail)

private theorem uniformHomeomorphismDecode_encode :
    ∀ h : BHist,
      uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformHomeomorphismFields : UniformHomeomorphismUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformHomeomorphismUp.mk X Y f g F G M N H C P L => [X, Y, f, g, F, G, M, N, H, C, P, L]

def uniformHomeomorphismToEventFlow : UniformHomeomorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformHomeomorphismFields x).map uniformHomeomorphismEncodeBHist

private def uniformHomeomorphismEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformHomeomorphismEventAtDefault index rest

def uniformHomeomorphismFromEventFlow (ef : EventFlow) : Option UniformHomeomorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformHomeomorphismUp.mk
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 0 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 1 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 2 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 3 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 4 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 5 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 6 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 7 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 8 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 9 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 10 ef))
      (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEventAtDefault 11 ef)))

private theorem uniformHomeomorphism_round_trip :
    ∀ x : UniformHomeomorphismUp,
      uniformHomeomorphismFromEventFlow (uniformHomeomorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y f g F G M N H C P L =>
      change
        some
          (UniformHomeomorphismUp.mk
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist X))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist Y))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist f))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist g))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist F))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist G))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist M))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist N))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist H))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist C))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist P))
            (uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist L))) =
          some (UniformHomeomorphismUp.mk X Y f g F G M N H C P L)
      rw [uniformHomeomorphismDecode_encode X, uniformHomeomorphismDecode_encode Y,
        uniformHomeomorphismDecode_encode f, uniformHomeomorphismDecode_encode g,
        uniformHomeomorphismDecode_encode F, uniformHomeomorphismDecode_encode G,
        uniformHomeomorphismDecode_encode M, uniformHomeomorphismDecode_encode N,
        uniformHomeomorphismDecode_encode H, uniformHomeomorphismDecode_encode C,
        uniformHomeomorphismDecode_encode P, uniformHomeomorphismDecode_encode L]

private theorem uniformHomeomorphismToEventFlow_injective
    {x y : UniformHomeomorphismUp} :
    uniformHomeomorphismToEventFlow x = uniformHomeomorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformHomeomorphismFromEventFlow (uniformHomeomorphismToEventFlow x) =
        uniformHomeomorphismFromEventFlow (uniformHomeomorphismToEventFlow y) :=
    congrArg uniformHomeomorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformHomeomorphism_round_trip x).symm
      (Eq.trans hread (uniformHomeomorphism_round_trip y)))

instance uniformHomeomorphismBHistCarrier :
    BHistCarrier UniformHomeomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformHomeomorphismToEventFlow
  fromEventFlow := uniformHomeomorphismFromEventFlow

instance uniformHomeomorphismChapterTasteGate :
    ChapterTasteGate UniformHomeomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformHomeomorphismFromEventFlow (uniformHomeomorphismToEventFlow x) = some x
    exact uniformHomeomorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformHomeomorphismToEventFlow_injective heq)

instance uniformHomeomorphismFieldFaithful :
    FieldFaithful UniformHomeomorphismUp where
  fields := uniformHomeomorphismFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk X₁ Y₁ f₁ g₁ F₁ G₁ M₁ N₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk X₂ Y₂ f₂ g₂ F₂ G₂ M₂ N₂ H₂ C₂ P₂ L₂ =>
        change [X₁, Y₁, f₁, g₁, F₁, G₁, M₁, N₁, H₁, C₁, P₁, L₁] =
          [X₂, Y₂, f₂, g₂, F₂, G₂, M₂, N₂, H₂, C₂, P₂, L₂] at h
        injection h with hX tail0
        injection tail0 with hY tail1
        injection tail1 with hf tail2
        injection tail2 with hg tail3
        injection tail3 with hF tail4
        injection tail4 with hG tail5
        injection tail5 with hM tail6
        injection tail6 with hN tail7
        injection tail7 with hH tail8
        injection tail8 with hC tail9
        injection tail9 with hP tail10
        injection tail10 with hL _
        subst hX
        subst hY
        subst hf
        subst hg
        subst hF
        subst hG
        subst hM
        subst hN
        subst hH
        subst hC
        subst hP
        subst hL
        rfl

instance uniformHomeomorphismNontrivial :
    Nontrivial UniformHomeomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformHomeomorphismUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformHomeomorphismUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformHomeomorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformHomeomorphismDecodeBHist (uniformHomeomorphismEncodeBHist h) = h) ∧
      (∀ x : UniformHomeomorphismUp,
        uniformHomeomorphismFromEventFlow (uniformHomeomorphismToEventFlow x) = some x) ∧
      (∀ x y : UniformHomeomorphismUp,
        uniformHomeomorphismToEventFlow x = uniformHomeomorphismToEventFlow y → x = y) ∧
      uniformHomeomorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨uniformHomeomorphismDecode_encode,
      uniformHomeomorphism_round_trip,
      fun _ _ heq => uniformHomeomorphismToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.UniformHomeomorphismUp
