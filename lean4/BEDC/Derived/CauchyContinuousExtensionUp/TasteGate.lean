import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuousExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContinuousExtensionUp : Type where
  | mk
      (source window tolerance mapRow extension uniqueness transport replay provenance
        name : BHist) :
      CauchyContinuousExtensionUp
  deriving DecidableEq

def cauchyContinuousExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuousExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuousExtensionEncodeBHist h

def cauchyContinuousExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuousExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuousExtensionDecodeBHist tail)

private theorem cauchyContinuousExtension_decode_encode_bhist :
    ∀ h : BHist,
      cauchyContinuousExtensionDecodeBHist
        (cauchyContinuousExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContinuousExtensionFields : CauchyContinuousExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuousExtensionUp.mk source window tolerance mapRow extension uniqueness
      transport replay provenance name =>
      [source, window, tolerance, mapRow, extension, uniqueness, transport, replay,
        provenance, name]

def cauchyContinuousExtensionToEventFlow :
    CauchyContinuousExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyContinuousExtensionFields x).map cauchyContinuousExtensionEncodeBHist

private def cauchyContinuousExtensionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyContinuousExtensionEventAtDefault index rest

def cauchyContinuousExtensionFromEventFlow
    (ef : EventFlow) : Option CauchyContinuousExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyContinuousExtensionUp.mk
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 0 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 1 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 2 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 3 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 4 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 5 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 6 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 7 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 8 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAtDefault 9 ef)))

private theorem cauchyContinuousExtension_round_trip :
    ∀ x : CauchyContinuousExtensionUp,
      cauchyContinuousExtensionFromEventFlow
        (cauchyContinuousExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source window tolerance mapRow extension uniqueness transport replay provenance name =>
      change
        some
          (CauchyContinuousExtensionUp.mk
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist source))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist window))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist tolerance))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist mapRow))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist extension))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist uniqueness))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist transport))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist replay))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist provenance))
            (cauchyContinuousExtensionDecodeBHist
              (cauchyContinuousExtensionEncodeBHist name))) =
          some
            (CauchyContinuousExtensionUp.mk source window tolerance mapRow extension
              uniqueness transport replay provenance name)
      rw [cauchyContinuousExtension_decode_encode_bhist source,
        cauchyContinuousExtension_decode_encode_bhist window,
        cauchyContinuousExtension_decode_encode_bhist tolerance,
        cauchyContinuousExtension_decode_encode_bhist mapRow,
        cauchyContinuousExtension_decode_encode_bhist extension,
        cauchyContinuousExtension_decode_encode_bhist uniqueness,
        cauchyContinuousExtension_decode_encode_bhist transport,
        cauchyContinuousExtension_decode_encode_bhist replay,
        cauchyContinuousExtension_decode_encode_bhist provenance,
        cauchyContinuousExtension_decode_encode_bhist name]

private theorem cauchyContinuousExtensionToEventFlow_injective
    {x y : CauchyContinuousExtensionUp} :
    cauchyContinuousExtensionToEventFlow x =
      cauchyContinuousExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuousExtensionFromEventFlow (cauchyContinuousExtensionToEventFlow x) =
        cauchyContinuousExtensionFromEventFlow (cauchyContinuousExtensionToEventFlow y) :=
    congrArg cauchyContinuousExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyContinuousExtension_round_trip x).symm
      (Eq.trans hread (cauchyContinuousExtension_round_trip y)))

private theorem cauchyContinuousExtension_field_faithful :
    ∀ x y : CauchyContinuousExtensionUp,
      cauchyContinuousExtensionFields x = cauchyContinuousExtensionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ window₁ tolerance₁ mapRow₁ extension₁ uniqueness₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk source₂ window₂ tolerance₂ mapRow₂ extension₂ uniqueness₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance cauchyContinuousExtensionBHistCarrier :
    BHistCarrier CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuousExtensionToEventFlow
  fromEventFlow := cauchyContinuousExtensionFromEventFlow

instance cauchyContinuousExtensionChapterTasteGate :
    ChapterTasteGate CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyContinuousExtensionFromEventFlow
        (cauchyContinuousExtensionToEventFlow x) = some x
    exact cauchyContinuousExtension_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyContinuousExtensionToEventFlow_injective heq)

instance cauchyContinuousExtensionFieldFaithful :
    FieldFaithful CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyContinuousExtensionFields
  field_faithful := cauchyContinuousExtension_field_faithful

instance cauchyContinuousExtensionNontrivial : Nontrivial CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyContinuousExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyContinuousExtensionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyContinuousExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyContinuousExtensionChapterTasteGate

theorem CauchyContinuousExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyContinuousExtensionDecodeBHist
        (cauchyContinuousExtensionEncodeBHist h) = h) ∧
      (∀ x : CauchyContinuousExtensionUp,
        cauchyContinuousExtensionFromEventFlow
          (cauchyContinuousExtensionToEventFlow x) = some x) ∧
        (∀ x y : CauchyContinuousExtensionUp,
          cauchyContinuousExtensionToEventFlow x =
            cauchyContinuousExtensionToEventFlow y → x = y) ∧
          cauchyContinuousExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyContinuousExtension_decode_encode_bhist,
      cauchyContinuousExtension_round_trip,
      (fun _ _ heq => cauchyContinuousExtensionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyContinuousExtensionUp
