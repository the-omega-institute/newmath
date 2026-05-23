import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformModulusUp : Type where
  | mk
      (tolerance precision bundleRow radius coverage pointwise foldLedger transport route
        provenance name : BHist) :
      UniformModulusUp
  deriving DecidableEq

def uniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformModulusEncodeBHist h

def uniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformModulusDecodeBHist tail)

private theorem uniformModulus_decode_encode_bhist :
    ∀ h : BHist, uniformModulusDecodeBHist (uniformModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformModulusFields : UniformModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformModulusUp.mk tolerance precision bundleRow radius coverage pointwise foldLedger
      transport route provenance name =>
      [tolerance, precision, bundleRow, radius, coverage, pointwise, foldLedger, transport,
        route, provenance, name]

def uniformModulusToEventFlow : UniformModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformModulusFields x).map uniformModulusEncodeBHist

private def uniformModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformModulusEventAtDefault index rest

def uniformModulusFromEventFlow (ef : EventFlow) : Option UniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformModulusUp.mk
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 0 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 1 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 2 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 3 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 4 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 5 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 6 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 7 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 8 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 9 ef))
      (uniformModulusDecodeBHist (uniformModulusEventAtDefault 10 ef)))

private theorem uniformModulus_round_trip :
    ∀ x : UniformModulusUp,
      uniformModulusFromEventFlow (uniformModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tolerance precision bundleRow radius coverage pointwise foldLedger transport route
      provenance name =>
      change
        some
          (UniformModulusUp.mk
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist tolerance))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist precision))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist bundleRow))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist radius))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist coverage))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist pointwise))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist foldLedger))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist transport))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist route))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist provenance))
            (uniformModulusDecodeBHist (uniformModulusEncodeBHist name))) =
          some
            (UniformModulusUp.mk tolerance precision bundleRow radius coverage pointwise
              foldLedger transport route provenance name)
      rw [uniformModulus_decode_encode_bhist tolerance,
        uniformModulus_decode_encode_bhist precision,
        uniformModulus_decode_encode_bhist bundleRow,
        uniformModulus_decode_encode_bhist radius,
        uniformModulus_decode_encode_bhist coverage,
        uniformModulus_decode_encode_bhist pointwise,
        uniformModulus_decode_encode_bhist foldLedger,
        uniformModulus_decode_encode_bhist transport,
        uniformModulus_decode_encode_bhist route,
        uniformModulus_decode_encode_bhist provenance,
        uniformModulus_decode_encode_bhist name]

private theorem uniformModulusToEventFlow_injective {x y : UniformModulusUp} :
    uniformModulusToEventFlow x = uniformModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformModulusFromEventFlow (uniformModulusToEventFlow x) =
        uniformModulusFromEventFlow (uniformModulusToEventFlow y) :=
    congrArg uniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformModulus_round_trip x).symm
      (Eq.trans hread (uniformModulus_round_trip y)))

private theorem uniformModulus_fields_faithful :
    ∀ x y : UniformModulusUp, uniformModulusFields x = uniformModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk t₁ p₁ b₁ r₁ c₁ m₁ f₁ l₁ q₁ v₁ n₁ =>
      cases y with
      | mk t₂ p₂ b₂ r₂ c₂ m₂ f₂ l₂ q₂ v₂ n₂ =>
          cases hfields
          rfl

instance uniformModulusBHistCarrier : BHistCarrier UniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformModulusToEventFlow
  fromEventFlow := uniformModulusFromEventFlow

instance uniformModulusChapterTasteGate : ChapterTasteGate UniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformModulusFromEventFlow (uniformModulusToEventFlow x) = some x
    exact uniformModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformModulusToEventFlow_injective heq)

instance uniformModulusFieldFaithful : FieldFaithful UniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformModulusFields
  field_faithful := uniformModulus_fields_faithful

instance uniformModulusNontrivial : Nontrivial UniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformModulusUp) ∧
      Nonempty (FieldFaithful UniformModulusUp) ∧
        Nonempty (Nontrivial UniformModulusUp) ∧
          (∀ h : BHist, uniformModulusDecodeBHist (uniformModulusEncodeBHist h) = h) ∧
            (∀ x : UniformModulusUp,
              uniformModulusFromEventFlow (uniformModulusToEventFlow x) = some x) ∧
              uniformModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨uniformModulusChapterTasteGate⟩,
      ⟨⟨uniformModulusFieldFaithful⟩,
        ⟨⟨uniformModulusNontrivial⟩,
          uniformModulus_decode_encode_bhist,
          uniformModulus_round_trip,
          rfl⟩⟩⟩

end BEDC.Derived.UniformModulusUp
