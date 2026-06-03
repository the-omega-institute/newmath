import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusAlgebraUp : Type where
  | mk (D W Q E S M U V H T P N : BHist) : RegularCauchyModulusAlgebraUp
  deriving DecidableEq

def regularCauchyModulusAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusAlgebraEncodeBHist h

def regularCauchyModulusAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusAlgebraDecodeBHist tail)

private theorem regularCauchyModulusAlgebra_decode_encode :
    ∀ h : BHist,
      regularCauchyModulusAlgebraDecodeBHist
          (regularCauchyModulusAlgebraEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyModulusAlgebraFields :
    RegularCauchyModulusAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusAlgebraUp.mk D W Q E S M U V H T P N =>
      [D, W, Q, E, S, M, U, V, H, T, P, N]

def regularCauchyModulusAlgebraToEventFlow :
    RegularCauchyModulusAlgebraUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyModulusAlgebraFields x).map regularCauchyModulusAlgebraEncodeBHist

private def regularCauchyModulusAlgebraEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyModulusAlgebraEventAt index rest

def regularCauchyModulusAlgebraFromEventFlow
    (ef : EventFlow) : Option RegularCauchyModulusAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyModulusAlgebraUp.mk
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 0 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 1 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 2 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 3 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 4 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 5 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 6 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 7 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 8 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 9 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 10 ef))
      (regularCauchyModulusAlgebraDecodeBHist (regularCauchyModulusAlgebraEventAt 11 ef)))

private theorem regularCauchyModulusAlgebra_round_trip :
    ∀ x : RegularCauchyModulusAlgebraUp,
      regularCauchyModulusAlgebraFromEventFlow
          (regularCauchyModulusAlgebraToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q E S M U V H T P N =>
      change
        some
          (RegularCauchyModulusAlgebraUp.mk
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist D))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist W))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist Q))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist E))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist S))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist M))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist U))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist V))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist H))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist T))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist P))
            (regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist N))) =
          some (RegularCauchyModulusAlgebraUp.mk D W Q E S M U V H T P N)
      rw [regularCauchyModulusAlgebra_decode_encode D,
        regularCauchyModulusAlgebra_decode_encode W,
        regularCauchyModulusAlgebra_decode_encode Q,
        regularCauchyModulusAlgebra_decode_encode E,
        regularCauchyModulusAlgebra_decode_encode S,
        regularCauchyModulusAlgebra_decode_encode M,
        regularCauchyModulusAlgebra_decode_encode U,
        regularCauchyModulusAlgebra_decode_encode V,
        regularCauchyModulusAlgebra_decode_encode H,
        regularCauchyModulusAlgebra_decode_encode T,
        regularCauchyModulusAlgebra_decode_encode P,
        regularCauchyModulusAlgebra_decode_encode N]

private theorem regularCauchyModulusAlgebraToEventFlow_injective
    {x y : RegularCauchyModulusAlgebraUp} :
    regularCauchyModulusAlgebraToEventFlow x =
        regularCauchyModulusAlgebraToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyModulusAlgebraFromEventFlow
          (regularCauchyModulusAlgebraToEventFlow x) =
        regularCauchyModulusAlgebraFromEventFlow
          (regularCauchyModulusAlgebraToEventFlow y) :=
    congrArg regularCauchyModulusAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyModulusAlgebra_round_trip x).symm
      (Eq.trans hread (regularCauchyModulusAlgebra_round_trip y)))

private theorem regularCauchyModulusAlgebra_fields_faithful :
    ∀ x y : RegularCauchyModulusAlgebraUp,
      regularCauchyModulusAlgebraFields x = regularCauchyModulusAlgebraFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ W₁ Q₁ E₁ S₁ M₁ U₁ V₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ Q₂ E₂ S₂ M₂ U₂ V₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyModulusAlgebraBHistCarrier :
    BHistCarrier RegularCauchyModulusAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusAlgebraToEventFlow
  fromEventFlow := regularCauchyModulusAlgebraFromEventFlow

instance regularCauchyModulusAlgebraChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusAlgebraFromEventFlow
          (regularCauchyModulusAlgebraToEventFlow x) =
        some x
    exact regularCauchyModulusAlgebra_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyModulusAlgebraToEventFlow_injective heq)

instance regularCauchyModulusAlgebraFieldFaithful :
    FieldFaithful RegularCauchyModulusAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyModulusAlgebraFields
  field_faithful := regularCauchyModulusAlgebra_fields_faithful

theorem RegularCauchyModulusAlgebraTasteGate_single_carrier_alignment :
    regularCauchyModulusAlgebraEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      regularCauchyModulusAlgebraEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ h : BHist,
          regularCauchyModulusAlgebraDecodeBHist
              (regularCauchyModulusAlgebraEncodeBHist h) =
            h) ∧
          Nonempty (BHistCarrier RegularCauchyModulusAlgebraUp) ∧
            Nonempty (ChapterTasteGate RegularCauchyModulusAlgebraUp) ∧
              Nonempty (FieldFaithful RegularCauchyModulusAlgebraUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨rfl, rfl, regularCauchyModulusAlgebra_decode_encode,
      ⟨regularCauchyModulusAlgebraBHistCarrier⟩,
      ⟨regularCauchyModulusAlgebraChapterTasteGate⟩,
      ⟨regularCauchyModulusAlgebraFieldFaithful⟩⟩

end BEDC.Derived.RegularCauchyModulusAlgebraUp
