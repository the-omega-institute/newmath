import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformSequentialContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformSequentialContinuityUp : Type where
  | mk (F M S WX WY RX RY DX DY EX EY H C P N : BHist) : UniformSequentialContinuityUp
  deriving DecidableEq

def uniformSequentialContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformSequentialContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformSequentialContinuityEncodeBHist h

def uniformSequentialContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformSequentialContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformSequentialContinuityDecodeBHist tail)

private theorem uniformSequentialContinuityDecodeEncodeBHist :
    ∀ h : BHist,
      uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformSequentialContinuityFields : UniformSequentialContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformSequentialContinuityUp.mk F M S WX WY RX RY DX DY EX EY H C P N =>
      [F, M, S, WX, WY, RX, RY, DX, DY, EX, EY, H, C, P, N]

def uniformSequentialContinuityToEventFlow : UniformSequentialContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformSequentialContinuityFields x).map uniformSequentialContinuityEncodeBHist

private def uniformSequentialContinuityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformSequentialContinuityEventAt index rest

def uniformSequentialContinuityFromEventFlow (ef : EventFlow) :
    Option UniformSequentialContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformSequentialContinuityUp.mk
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 0 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 1 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 2 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 3 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 4 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 5 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 6 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 7 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 8 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 9 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 10 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 11 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 12 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 13 ef))
      (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEventAt 14 ef)))

private theorem uniformSequentialContinuity_round_trip
    (x : UniformSequentialContinuityUp) :
    uniformSequentialContinuityFromEventFlow
      (uniformSequentialContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F M S WX WY RX RY DX DY EX EY H C P N =>
      change
        some
          (UniformSequentialContinuityUp.mk
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist F))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist M))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist S))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist WX))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist WY))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist RX))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist RY))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist DX))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist DY))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist EX))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist EY))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist H))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist C))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist P))
            (uniformSequentialContinuityDecodeBHist (uniformSequentialContinuityEncodeBHist N))) =
          some (UniformSequentialContinuityUp.mk F M S WX WY RX RY DX DY EX EY H C P N)
      rw [uniformSequentialContinuityDecodeEncodeBHist F,
        uniformSequentialContinuityDecodeEncodeBHist M,
        uniformSequentialContinuityDecodeEncodeBHist S,
        uniformSequentialContinuityDecodeEncodeBHist WX,
        uniformSequentialContinuityDecodeEncodeBHist WY,
        uniformSequentialContinuityDecodeEncodeBHist RX,
        uniformSequentialContinuityDecodeEncodeBHist RY,
        uniformSequentialContinuityDecodeEncodeBHist DX,
        uniformSequentialContinuityDecodeEncodeBHist DY,
        uniformSequentialContinuityDecodeEncodeBHist EX,
        uniformSequentialContinuityDecodeEncodeBHist EY,
        uniformSequentialContinuityDecodeEncodeBHist H,
        uniformSequentialContinuityDecodeEncodeBHist C,
        uniformSequentialContinuityDecodeEncodeBHist P,
        uniformSequentialContinuityDecodeEncodeBHist N]

private theorem uniformSequentialContinuityToEventFlow_injective
    {x y : UniformSequentialContinuityUp} :
    uniformSequentialContinuityToEventFlow x = uniformSequentialContinuityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformSequentialContinuityFromEventFlow (uniformSequentialContinuityToEventFlow x) =
        uniformSequentialContinuityFromEventFlow (uniformSequentialContinuityToEventFlow y) :=
    congrArg uniformSequentialContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformSequentialContinuity_round_trip x).symm
      (Eq.trans hread (uniformSequentialContinuity_round_trip y)))

private theorem uniformSequentialContinuity_fields_faithful :
    ∀ x y : UniformSequentialContinuityUp,
      uniformSequentialContinuityFields x = uniformSequentialContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ M₁ S₁ WX₁ WY₁ RX₁ RY₁ DX₁ DY₁ EX₁ EY₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ M₂ S₂ WX₂ WY₂ RX₂ RY₂ DX₂ DY₂ EX₂ EY₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance uniformSequentialContinuityBHistCarrier :
    BHistCarrier UniformSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformSequentialContinuityToEventFlow
  fromEventFlow := uniformSequentialContinuityFromEventFlow

instance uniformSequentialContinuityChapterTasteGate :
    ChapterTasteGate UniformSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformSequentialContinuityFromEventFlow (uniformSequentialContinuityToEventFlow x) =
        some x
    exact uniformSequentialContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformSequentialContinuityToEventFlow_injective heq)

instance uniformSequentialContinuityFieldFaithful :
    FieldFaithful UniformSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformSequentialContinuityFields
  field_faithful := uniformSequentialContinuity_fields_faithful

instance uniformSequentialContinuityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UniformSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformSequentialContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformSequentialContinuityUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformSequentialContinuityUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformSequentialContinuityUp) ∧
      Nonempty (FieldFaithful UniformSequentialContinuityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial UniformSequentialContinuityUp) ∧
          (∀ h : BHist,
            uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist h) = h) ∧
            (∀ x : UniformSequentialContinuityUp,
              uniformSequentialContinuityFromEventFlow
                (uniformSequentialContinuityToEventFlow x) = some x) ∧
              (∀ x y : UniformSequentialContinuityUp,
                uniformSequentialContinuityToEventFlow x =
                  uniformSequentialContinuityToEventFlow y → x = y) ∧
                uniformSequentialContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨uniformSequentialContinuityChapterTasteGate⟩,
      ⟨uniformSequentialContinuityFieldFaithful⟩,
      ⟨uniformSequentialContinuityNontrivial⟩,
      uniformSequentialContinuityDecodeEncodeBHist,
      uniformSequentialContinuity_round_trip,
      (fun _ _ heq => uniformSequentialContinuityToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformSequentialContinuityUp
