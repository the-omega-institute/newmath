import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySchwarzRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySchwarzRealUp : Type where
  | mk (V X Y I A B D Q S E H T P N : BHist) : CauchySchwarzRealUp
  deriving DecidableEq

def cauchySchwarzRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySchwarzRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySchwarzRealEncodeBHist h

def cauchySchwarzRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySchwarzRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySchwarzRealDecodeBHist tail)

private theorem cauchySchwarzRealDecode_encode :
    ∀ h : BHist, cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySchwarzRealFields : CauchySchwarzRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySchwarzRealUp.mk V X Y I A B D Q S E H T P N =>
      [V, X, Y, I, A, B, D, Q, S, E, H, T, P, N]

def cauchySchwarzRealToEventFlow : CauchySchwarzRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchySchwarzRealEncodeBHist (cauchySchwarzRealFields x)

private def cauchySchwarzRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySchwarzRealEventAtDefault index rest

def cauchySchwarzRealFromEventFlow : EventFlow → Option CauchySchwarzRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchySchwarzRealUp.mk
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 0 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 1 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 2 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 3 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 4 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 5 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 6 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 7 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 8 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 9 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 10 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 11 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 12 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 13 ef)))

private theorem cauchySchwarzReal_round_trip :
    ∀ x : CauchySchwarzRealUp,
      cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V X Y I A B D Q S E H T P N =>
      change
        some
          (CauchySchwarzRealUp.mk
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist V))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist X))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist Y))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist I))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist A))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist B))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist D))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist Q))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist S))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist E))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist H))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist T))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist P))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist N))) =
          some (CauchySchwarzRealUp.mk V X Y I A B D Q S E H T P N)
      rw [cauchySchwarzRealDecode_encode V, cauchySchwarzRealDecode_encode X,
        cauchySchwarzRealDecode_encode Y, cauchySchwarzRealDecode_encode I,
        cauchySchwarzRealDecode_encode A, cauchySchwarzRealDecode_encode B,
        cauchySchwarzRealDecode_encode D, cauchySchwarzRealDecode_encode Q,
        cauchySchwarzRealDecode_encode S, cauchySchwarzRealDecode_encode E,
        cauchySchwarzRealDecode_encode H, cauchySchwarzRealDecode_encode T,
        cauchySchwarzRealDecode_encode P, cauchySchwarzRealDecode_encode N]

private theorem cauchySchwarzRealToEventFlow_injective {x y : CauchySchwarzRealUp} :
    cauchySchwarzRealToEventFlow x = cauchySchwarzRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) =
        cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow y) :=
    congrArg cauchySchwarzRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySchwarzReal_round_trip x).symm
      (Eq.trans hread (cauchySchwarzReal_round_trip y)))

private theorem cauchySchwarzReal_field_faithful :
    ∀ x y : CauchySchwarzRealUp, cauchySchwarzRealFields x = cauchySchwarzRealFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk V₁ X₁ Y₁ I₁ A₁ B₁ D₁ Q₁ S₁ E₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk V₂ X₂ Y₂ I₂ A₂ B₂ D₂ Q₂ S₂ E₂ H₂ T₂ P₂ N₂ =>
          cases h
          rfl

instance cauchySchwarzRealBHistCarrier : BHistCarrier CauchySchwarzRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySchwarzRealToEventFlow
  fromEventFlow := cauchySchwarzRealFromEventFlow

instance cauchySchwarzRealChapterTasteGate : ChapterTasteGate CauchySchwarzRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x
    exact cauchySchwarzReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySchwarzRealToEventFlow_injective heq)

instance cauchySchwarzRealFieldFaithful : FieldFaithful CauchySchwarzRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySchwarzRealFields
  field_faithful := cauchySchwarzReal_field_faithful

def taste_gate : ChapterTasteGate CauchySchwarzRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySchwarzRealChapterTasteGate

theorem CauchySchwarzRealUp_single_carrier_alignment :
    (∀ h : BHist, cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist h) = h) ∧
      (∀ x : CauchySchwarzRealUp,
        cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x) ∧
      (∀ x y : CauchySchwarzRealUp,
        cauchySchwarzRealToEventFlow x = cauchySchwarzRealToEventFlow y → x = y) ∧
      cauchySchwarzRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchySchwarzRealDecode_encode,
      cauchySchwarzReal_round_trip,
      (fun _ _ heq => cauchySchwarzRealToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchySchwarzRealUp
