import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformInverseModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformInverseModulusUp : Type where
  | mk (X Y F G E N R M T H C P A : BHist) : UniformInverseModulusUp
  deriving DecidableEq

def uniformInverseModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformInverseModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformInverseModulusEncodeBHist h

def uniformInverseModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformInverseModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformInverseModulusDecodeBHist tail)

private theorem UniformInverseModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformInverseModulusFields : UniformInverseModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformInverseModulusUp.mk X Y F G E N R M T H C P A => [X, Y, F, G, E, N, R, M, T, H, C, P, A]

def uniformInverseModulusToEventFlow : UniformInverseModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformInverseModulusFields x).map uniformInverseModulusEncodeBHist

private def uniformInverseModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformInverseModulusEventAtDefault index rest

def uniformInverseModulusFromEventFlow : EventFlow → Option UniformInverseModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (UniformInverseModulusUp.mk
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 0 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 1 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 2 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 3 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 4 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 5 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 6 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 7 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 8 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 9 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 10 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 11 ef))
          (uniformInverseModulusDecodeBHist (uniformInverseModulusEventAtDefault 12 ef)))

private theorem UniformInverseModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformInverseModulusUp,
      uniformInverseModulusFromEventFlow (uniformInverseModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y F G E N R M T H C P A =>
      change
        some
          (UniformInverseModulusUp.mk
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist X))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist Y))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist F))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist G))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist E))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist N))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist R))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist M))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist T))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist H))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist C))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist P))
            (uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist A))) =
          some (UniformInverseModulusUp.mk X Y F G E N R M T H C P A)
      rw [UniformInverseModulusTasteGate_single_carrier_alignment_decode X,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode Y,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode F,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode G,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode E,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode N,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode R,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode M,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode T,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode H,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode C,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode P,
        UniformInverseModulusTasteGate_single_carrier_alignment_decode A]

private theorem UniformInverseModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformInverseModulusUp} :
    uniformInverseModulusToEventFlow x = uniformInverseModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformInverseModulusFromEventFlow (uniformInverseModulusToEventFlow x) =
        uniformInverseModulusFromEventFlow (uniformInverseModulusToEventFlow y) :=
    congrArg uniformInverseModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformInverseModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformInverseModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformInverseModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformInverseModulusUp, uniformInverseModulusFields x = uniformInverseModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ F₁ G₁ E₁ N₁ R₁ M₁ T₁ H₁ C₁ P₁ A₁ =>
      cases y with
      | mk X₂ Y₂ F₂ G₂ E₂ N₂ R₂ M₂ T₂ H₂ C₂ P₂ A₂ =>
          cases hfields
          rfl

instance uniformInverseModulusBHistCarrier : BHistCarrier UniformInverseModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformInverseModulusToEventFlow
  fromEventFlow := uniformInverseModulusFromEventFlow

instance uniformInverseModulusChapterTasteGate : ChapterTasteGate UniformInverseModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformInverseModulusFromEventFlow (uniformInverseModulusToEventFlow x) = some x
    exact UniformInverseModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformInverseModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformInverseModulusFieldFaithful : FieldFaithful UniformInverseModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformInverseModulusFields
  field_faithful := UniformInverseModulusTasteGate_single_carrier_alignment_fields

instance uniformInverseModulusNontrivial : Nontrivial UniformInverseModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformInverseModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformInverseModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformInverseModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformInverseModulusChapterTasteGate

theorem UniformInverseModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformInverseModulusDecodeBHist (uniformInverseModulusEncodeBHist h) = h) ∧
      (∀ x : UniformInverseModulusUp,
        uniformInverseModulusFromEventFlow (uniformInverseModulusToEventFlow x) = some x) ∧
        (∀ x y : UniformInverseModulusUp,
          uniformInverseModulusToEventFlow x = uniformInverseModulusToEventFlow y → x = y) ∧
          uniformInverseModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨UniformInverseModulusTasteGate_single_carrier_alignment_decode,
      UniformInverseModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformInverseModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformInverseModulusUp
