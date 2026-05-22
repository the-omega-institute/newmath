import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealFunctionUniformCauchyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealFunctionUniformCauchyUp : Type where
  | mk (A S M D R E H C P N : BHist) : RealFunctionUniformCauchyUp
  deriving DecidableEq

def realFunctionUniformCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realFunctionUniformCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realFunctionUniformCauchyEncodeBHist h

def realFunctionUniformCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realFunctionUniformCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realFunctionUniformCauchyDecodeBHist tail)

private theorem realFunctionUniformCauchyDecode_encode :
    ∀ h : BHist,
      realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realFunctionUniformCauchyFields : RealFunctionUniformCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealFunctionUniformCauchyUp.mk A S M D R E H C P N => [A, S, M, D, R, E, H, C, P, N]

def realFunctionUniformCauchyToEventFlow : RealFunctionUniformCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realFunctionUniformCauchyEncodeBHist (realFunctionUniformCauchyFields x)

private def realFunctionUniformCauchyRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realFunctionUniformCauchyRawAt index rest

def realFunctionUniformCauchyFromEventFlow
    (flow : EventFlow) : Option RealFunctionUniformCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealFunctionUniformCauchyUp.mk
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 0 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 1 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 2 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 3 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 4 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 5 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 6 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 7 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 8 flow))
      (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyRawAt 9 flow)))

private theorem realFunctionUniformCauchy_round_trip :
    ∀ x : RealFunctionUniformCauchyUp,
      realFunctionUniformCauchyFromEventFlow (realFunctionUniformCauchyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A S M D R E H C P N =>
      change
        some
          (RealFunctionUniformCauchyUp.mk
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist A))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist S))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist M))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist D))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist R))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist E))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist H))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist C))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist P))
            (realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist N))) =
          some (RealFunctionUniformCauchyUp.mk A S M D R E H C P N)
      rw [realFunctionUniformCauchyDecode_encode A, realFunctionUniformCauchyDecode_encode S,
        realFunctionUniformCauchyDecode_encode M, realFunctionUniformCauchyDecode_encode D,
        realFunctionUniformCauchyDecode_encode R, realFunctionUniformCauchyDecode_encode E,
        realFunctionUniformCauchyDecode_encode H, realFunctionUniformCauchyDecode_encode C,
        realFunctionUniformCauchyDecode_encode P, realFunctionUniformCauchyDecode_encode N]

private theorem realFunctionUniformCauchyToEventFlow_injective
    {x y : RealFunctionUniformCauchyUp} :
    realFunctionUniformCauchyToEventFlow x = realFunctionUniformCauchyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realFunctionUniformCauchyFromEventFlow (realFunctionUniformCauchyToEventFlow x) =
        realFunctionUniformCauchyFromEventFlow (realFunctionUniformCauchyToEventFlow y) :=
    congrArg realFunctionUniformCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realFunctionUniformCauchy_round_trip x).symm
      (Eq.trans hread (realFunctionUniformCauchy_round_trip y)))

private theorem realFunctionUniformCauchy_fields_faithful :
    ∀ x y : RealFunctionUniformCauchyUp,
      realFunctionUniformCauchyFields x = realFunctionUniformCauchyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk A₁ S₁ M₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ S₂ M₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          simp only [realFunctionUniformCauchyFields] at h
          cases h
          rfl

instance realFunctionUniformCauchyBHistCarrier :
    BHistCarrier RealFunctionUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realFunctionUniformCauchyToEventFlow
  fromEventFlow := realFunctionUniformCauchyFromEventFlow

instance realFunctionUniformCauchyChapterTasteGate :
    ChapterTasteGate RealFunctionUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realFunctionUniformCauchyFromEventFlow (realFunctionUniformCauchyToEventFlow x) = some x
    exact realFunctionUniformCauchy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realFunctionUniformCauchyToEventFlow_injective heq)

instance realFunctionUniformCauchyFieldFaithful :
    FieldFaithful RealFunctionUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realFunctionUniformCauchyFields
  field_faithful := realFunctionUniformCauchy_fields_faithful

instance realFunctionUniformCauchyNontrivial :
    Nontrivial RealFunctionUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealFunctionUniformCauchyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealFunctionUniformCauchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealFunctionUniformCauchyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealFunctionUniformCauchyUp) ∧
      Nonempty (FieldFaithful RealFunctionUniformCauchyUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealFunctionUniformCauchyUp) ∧
          (∀ h : BHist,
            realFunctionUniformCauchyDecodeBHist (realFunctionUniformCauchyEncodeBHist h) = h) ∧
            (∀ x : RealFunctionUniformCauchyUp,
              realFunctionUniformCauchyFromEventFlow
                  (realFunctionUniformCauchyToEventFlow x) =
                some x) ∧
              (∀ x y : RealFunctionUniformCauchyUp,
                realFunctionUniformCauchyToEventFlow x =
                    realFunctionUniformCauchyToEventFlow y →
                  x = y) ∧
                realFunctionUniformCauchyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨realFunctionUniformCauchyChapterTasteGate⟩,
      ⟨realFunctionUniformCauchyFieldFaithful⟩,
      ⟨realFunctionUniformCauchyNontrivial⟩,
      realFunctionUniformCauchyDecode_encode,
      realFunctionUniformCauchy_round_trip,
      by
        intro x y heq
        exact realFunctionUniformCauchyToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealFunctionUniformCauchyUp.TasteGate
