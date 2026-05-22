import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitContinuousUp : Type where
  | mk
      (continuousFamily uniformLimitRow sharedModulus finiteWindows regularHandoff endpointSeal
        transports continuations provenance localNameCert : BHist) :
      UniformLimitContinuousUp
  deriving DecidableEq

def uniformLimitContinuousEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitContinuousEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitContinuousEncodeBHist h

def uniformLimitContinuousDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitContinuousDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitContinuousDecodeBHist tail)

private theorem uniformLimitContinuous_decode_encode_bhist :
    ∀ h : BHist, uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLimitContinuousFields : UniformLimitContinuousUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitContinuousUp.mk continuousFamily uniformLimitRow sharedModulus finiteWindows
      regularHandoff endpointSeal transports continuations provenance localNameCert =>
      [continuousFamily, uniformLimitRow, sharedModulus, finiteWindows, regularHandoff,
        endpointSeal, transports, continuations, provenance, localNameCert]

def uniformLimitContinuousToEventFlow : UniformLimitContinuousUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformLimitContinuousFields x).map uniformLimitContinuousEncodeBHist

private def uniformLimitContinuousEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformLimitContinuousEventAtDefault index rest

def uniformLimitContinuousFromEventFlow : EventFlow → Option UniformLimitContinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (UniformLimitContinuousUp.mk
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 0 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 1 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 2 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 3 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 4 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 5 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 6 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 7 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 8 ef))
        (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEventAtDefault 9 ef)))

private theorem uniformLimitContinuous_round_trip :
    ∀ x : UniformLimitContinuousUp,
      uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk continuousFamily uniformLimitRow sharedModulus finiteWindows regularHandoff
      endpointSeal transports continuations provenance localNameCert =>
      change
        some
          (UniformLimitContinuousUp.mk
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist continuousFamily))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist uniformLimitRow))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist sharedModulus))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist finiteWindows))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist regularHandoff))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist endpointSeal))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist transports))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist continuations))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist provenance))
            (uniformLimitContinuousDecodeBHist
              (uniformLimitContinuousEncodeBHist localNameCert))) =
          some
            (UniformLimitContinuousUp.mk continuousFamily uniformLimitRow sharedModulus
              finiteWindows regularHandoff endpointSeal transports continuations provenance
              localNameCert)
      rw [uniformLimitContinuous_decode_encode_bhist continuousFamily,
        uniformLimitContinuous_decode_encode_bhist uniformLimitRow,
        uniformLimitContinuous_decode_encode_bhist sharedModulus,
        uniformLimitContinuous_decode_encode_bhist finiteWindows,
        uniformLimitContinuous_decode_encode_bhist regularHandoff,
        uniformLimitContinuous_decode_encode_bhist endpointSeal,
        uniformLimitContinuous_decode_encode_bhist transports,
        uniformLimitContinuous_decode_encode_bhist continuations,
        uniformLimitContinuous_decode_encode_bhist provenance,
        uniformLimitContinuous_decode_encode_bhist localNameCert]

private theorem uniformLimitContinuousToEventFlow_injective {x y : UniformLimitContinuousUp} :
    uniformLimitContinuousToEventFlow x = uniformLimitContinuousToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) =
        uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow y) :=
    congrArg uniformLimitContinuousFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformLimitContinuous_round_trip x).symm
      (Eq.trans hread (uniformLimitContinuous_round_trip y)))

private theorem uniformLimitContinuous_field_faithful :
    ∀ x y : UniformLimitContinuousUp, uniformLimitContinuousFields x =
      uniformLimitContinuousFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk continuousFamily₁ uniformLimitRow₁ sharedModulus₁ finiteWindows₁ regularHandoff₁
      endpointSeal₁ transports₁ continuations₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk continuousFamily₂ uniformLimitRow₂ sharedModulus₂ finiteWindows₂ regularHandoff₂
          endpointSeal₂ transports₂ continuations₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance uniformLimitContinuousBHistCarrier : BHistCarrier UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitContinuousToEventFlow
  fromEventFlow := uniformLimitContinuousFromEventFlow

instance uniformLimitContinuousChapterTasteGate : ChapterTasteGate UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) = some x
    exact uniformLimitContinuous_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLimitContinuousToEventFlow_injective heq)

instance uniformLimitContinuousFieldFaithful : FieldFaithful UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitContinuousFields
  field_faithful := uniformLimitContinuous_field_faithful

instance uniformLimitContinuousNontrivial : Nontrivial UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLimitContinuousUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLimitContinuousUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformLimitContinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitContinuousChapterTasteGate

theorem UniformLimitContinuousTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist h) = h) ∧
      (∀ x : UniformLimitContinuousUp,
        uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) = some x) ∧
        (∀ x y : UniformLimitContinuousUp,
          uniformLimitContinuousToEventFlow x = uniformLimitContinuousToEventFlow y → x = y) ∧
          uniformLimitContinuousEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨uniformLimitContinuous_decode_encode_bhist,
      uniformLimitContinuous_round_trip,
      (fun _ _ heq => uniformLimitContinuousToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformLimitContinuousUp
