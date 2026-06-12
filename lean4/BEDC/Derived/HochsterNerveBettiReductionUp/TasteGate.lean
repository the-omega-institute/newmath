import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HochsterNerveBettiReductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HochsterNerveBettiReductionUp : Type where
  | mk (V F N H0 B0 G T P L : BHist) : HochsterNerveBettiReductionUp
  deriving DecidableEq

def hochsterNerveBettiReductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hochsterNerveBettiReductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hochsterNerveBettiReductionEncodeBHist h

def hochsterNerveBettiReductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hochsterNerveBettiReductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hochsterNerveBettiReductionDecodeBHist tail)

private theorem hochsterNerveBettiReduction_decode_encode_bhist :
    ∀ h : BHist,
      hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hochsterNerveBettiReductionFields : HochsterNerveBettiReductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HochsterNerveBettiReductionUp.mk V F N H0 B0 G T P L => [V, F, N, H0, B0, G, T, P, L]

def hochsterNerveBettiReductionToEventFlow : HochsterNerveBettiReductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hochsterNerveBettiReductionFields x).map hochsterNerveBettiReductionEncodeBHist

private def hochsterNerveBettiReductionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hochsterNerveBettiReductionEventAtDefault index rest

def hochsterNerveBettiReductionFromEventFlow
    (ef : EventFlow) : Option HochsterNerveBettiReductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HochsterNerveBettiReductionUp.mk
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 0 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 1 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 2 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 3 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 4 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 5 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 6 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 7 ef))
      (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEventAtDefault 8 ef)))

private theorem hochsterNerveBettiReduction_round_trip
    (x : HochsterNerveBettiReductionUp) :
    hochsterNerveBettiReductionFromEventFlow
      (hochsterNerveBettiReductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk V F N H0 B0 G T P L =>
      change
        some
          (HochsterNerveBettiReductionUp.mk
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist V))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist F))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist N))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist H0))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist B0))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist G))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist T))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist P))
            (hochsterNerveBettiReductionDecodeBHist (hochsterNerveBettiReductionEncodeBHist L))) =
          some (HochsterNerveBettiReductionUp.mk V F N H0 B0 G T P L)
      rw [hochsterNerveBettiReduction_decode_encode_bhist V,
        hochsterNerveBettiReduction_decode_encode_bhist F,
        hochsterNerveBettiReduction_decode_encode_bhist N,
        hochsterNerveBettiReduction_decode_encode_bhist H0,
        hochsterNerveBettiReduction_decode_encode_bhist B0,
        hochsterNerveBettiReduction_decode_encode_bhist G,
        hochsterNerveBettiReduction_decode_encode_bhist T,
        hochsterNerveBettiReduction_decode_encode_bhist P,
        hochsterNerveBettiReduction_decode_encode_bhist L]

private theorem hochsterNerveBettiReductionToEventFlow_injective
    {x y : HochsterNerveBettiReductionUp} :
    hochsterNerveBettiReductionToEventFlow x = hochsterNerveBettiReductionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hochsterNerveBettiReductionFromEventFlow (hochsterNerveBettiReductionToEventFlow x) =
        hochsterNerveBettiReductionFromEventFlow (hochsterNerveBettiReductionToEventFlow y) :=
    congrArg hochsterNerveBettiReductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hochsterNerveBettiReduction_round_trip x).symm
      (Eq.trans hread (hochsterNerveBettiReduction_round_trip y)))

private theorem hochsterNerveBettiReduction_fields_faithful :
    ∀ x y : HochsterNerveBettiReductionUp,
      hochsterNerveBettiReductionFields x = hochsterNerveBettiReductionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk V₁ F₁ N₁ H0₁ B0₁ G₁ T₁ P₁ L₁ =>
      cases y with
      | mk V₂ F₂ N₂ H0₂ B0₂ G₂ T₂ P₂ L₂ =>
          injection h with hV t1
          injection t1 with hF t2
          injection t2 with hN t3
          injection t3 with hH0 t4
          injection t4 with hB0 t5
          injection t5 with hG t6
          injection t6 with hT t7
          injection t7 with hP t8
          injection t8 with hL _
          cases hV
          cases hF
          cases hN
          cases hH0
          cases hB0
          cases hG
          cases hT
          cases hP
          cases hL
          rfl

instance hochsterNerveBettiReductionBHistCarrier :
    BHistCarrier HochsterNerveBettiReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hochsterNerveBettiReductionToEventFlow
  fromEventFlow := hochsterNerveBettiReductionFromEventFlow

instance hochsterNerveBettiReductionChapterTasteGate :
    ChapterTasteGate HochsterNerveBettiReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hochsterNerveBettiReductionFromEventFlow (hochsterNerveBettiReductionToEventFlow x) =
        some x
    exact hochsterNerveBettiReduction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hochsterNerveBettiReductionToEventFlow_injective heq)

instance hochsterNerveBettiReductionFieldFaithful :
    FieldFaithful HochsterNerveBettiReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hochsterNerveBettiReductionFields
  field_faithful := hochsterNerveBettiReduction_fields_faithful

instance hochsterNerveBettiReductionNontrivial :
    Nontrivial HochsterNerveBettiReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HochsterNerveBettiReductionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HochsterNerveBettiReductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HochsterNerveBettiReduction_taste_gate :
    ChapterTasteGate HochsterNerveBettiReductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hochsterNerveBettiReductionChapterTasteGate

end BEDC.Derived.HochsterNerveBettiReductionUp
