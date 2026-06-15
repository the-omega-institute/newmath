import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineBorelLocatedIntervalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineBorelLocatedIntervalUp : Type where
  | mk (I E R S D F K H C P N : BHist) : HeineBorelLocatedIntervalUp
  deriving DecidableEq

def heineBorelLocatedIntervalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineBorelLocatedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineBorelLocatedIntervalEncodeBHist h

def heineBorelLocatedIntervalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineBorelLocatedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineBorelLocatedIntervalDecodeBHist tail)

theorem HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heineBorelLocatedIntervalFields :
    HeineBorelLocatedIntervalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeineBorelLocatedIntervalUp.mk I E R S D F K H C P N =>
      [I, E, R, S, D, F, K, H, C, P, N]

def heineBorelLocatedIntervalToEventFlow :
    HeineBorelLocatedIntervalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (heineBorelLocatedIntervalFields x).map
        heineBorelLocatedIntervalEncodeBHist

def heineBorelLocatedIntervalEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      heineBorelLocatedIntervalEventAtDefault index rest

def heineBorelLocatedIntervalFromEventFlow
    (ef : EventFlow) : Option HeineBorelLocatedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HeineBorelLocatedIntervalUp.mk
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 0 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 1 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 2 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 3 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 4 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 5 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 6 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 7 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 8 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 9 ef))
      (heineBorelLocatedIntervalDecodeBHist
        (heineBorelLocatedIntervalEventAtDefault 10 ef)))

theorem HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_round_trip :
    forall x : HeineBorelLocatedIntervalUp,
      heineBorelLocatedIntervalFromEventFlow
        (heineBorelLocatedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I E R S D F K H C P N =>
      change
        some
          (HeineBorelLocatedIntervalUp.mk
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist I))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist E))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist R))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist S))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist D))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist F))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist K))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist H))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist C))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist P))
            (heineBorelLocatedIntervalDecodeBHist
              (heineBorelLocatedIntervalEncodeBHist N))) =
          some (HeineBorelLocatedIntervalUp.mk I E R S D F K H C P N)
      rw [HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode I,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode E,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode R,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode S,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode D,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode F,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode K,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode H,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode C,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode P,
        HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode N]

theorem HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HeineBorelLocatedIntervalUp} :
    heineBorelLocatedIntervalToEventFlow x =
      heineBorelLocatedIntervalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineBorelLocatedIntervalFromEventFlow
          (heineBorelLocatedIntervalToEventFlow x) =
        heineBorelLocatedIntervalFromEventFlow
          (heineBorelLocatedIntervalToEventFlow y) :=
    congrArg heineBorelLocatedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_round_trip y)))

theorem HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_field_faithful :
    forall x y : HeineBorelLocatedIntervalUp,
      heineBorelLocatedIntervalFields x =
        heineBorelLocatedIntervalFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ E₁ R₁ S₁ D₁ F₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ E₂ R₂ S₂ D₂ F₂ K₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance heineBorelLocatedIntervalBHistCarrier :
    BHistCarrier HeineBorelLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineBorelLocatedIntervalToEventFlow
  fromEventFlow := heineBorelLocatedIntervalFromEventFlow

instance heineBorelLocatedIntervalChapterTasteGate :
    ChapterTasteGate HeineBorelLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id
      (HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance heineBorelLocatedIntervalFieldFaithful :
    FieldFaithful HeineBorelLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := heineBorelLocatedIntervalFields
  field_faithful :=
    HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_field_faithful

def heineBorelLocatedIntervalTasteGate :
    ChapterTasteGate HeineBorelLocatedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heineBorelLocatedIntervalChapterTasteGate

theorem HeineBorelLocatedIntervalTasteGate_single_carrier_alignment :
    (heineBorelLocatedIntervalEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (∀ h : BHist,
        heineBorelLocatedIntervalDecodeBHist
          (heineBorelLocatedIntervalEncodeBHist h) = h) ∧
      (∀ x : HeineBorelLocatedIntervalUp,
        heineBorelLocatedIntervalFromEventFlow
          (heineBorelLocatedIntervalToEventFlow x) = some x) ∧
      (∀ x y : HeineBorelLocatedIntervalUp,
        heineBorelLocatedIntervalFields x =
          heineBorelLocatedIntervalFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_decode_encode,
      HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_round_trip,
      HeineBorelLocatedIntervalTasteGate_single_carrier_alignment_field_faithful⟩

end BEDC.Derived.HeineBorelLocatedIntervalUp.TasteGate
