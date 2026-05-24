import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InverseMappingTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InverseMappingTheoremUp : Type where
  | mk (X Y T B I H C P N : BHist) : InverseMappingTheoremUp
  deriving DecidableEq

def inverseMappingTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inverseMappingTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inverseMappingTheoremEncodeBHist h

def inverseMappingTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inverseMappingTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inverseMappingTheoremDecodeBHist tail)

private theorem InverseMappingTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def inverseMappingTheoremFields : InverseMappingTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InverseMappingTheoremUp.mk X Y T B I H C P N => [X, Y, T, B, I, H, C, P, N]

def inverseMappingTheoremToEventFlow : InverseMappingTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InverseMappingTheoremUp.mk X Y T B I H C P N =>
      [inverseMappingTheoremEncodeBHist X, inverseMappingTheoremEncodeBHist Y,
        inverseMappingTheoremEncodeBHist T, inverseMappingTheoremEncodeBHist B,
        inverseMappingTheoremEncodeBHist I, inverseMappingTheoremEncodeBHist H,
        inverseMappingTheoremEncodeBHist C, inverseMappingTheoremEncodeBHist P,
        inverseMappingTheoremEncodeBHist N]

private def inverseMappingTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => inverseMappingTheoremEventAtDefault index rest

def inverseMappingTheoremFromEventFlow
    (ef : EventFlow) : Option InverseMappingTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (InverseMappingTheoremUp.mk
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 0 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 1 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 2 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 3 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 4 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 5 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 6 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 7 ef))
      (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEventAtDefault 8 ef)))

private theorem InverseMappingTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : InverseMappingTheoremUp,
      inverseMappingTheoremFromEventFlow (inverseMappingTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y T B I H C P N =>
      change
        some
          (InverseMappingTheoremUp.mk
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist X))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist Y))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist T))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist B))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist I))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist H))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist C))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist P))
            (inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist N))) =
          some (InverseMappingTheoremUp.mk X Y T B I H C P N)
      rw [InverseMappingTheoremTasteGate_single_carrier_alignment_decode X,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode Y,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode T,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode B,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode I,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode H,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode C,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode P,
        InverseMappingTheoremTasteGate_single_carrier_alignment_decode N]

private theorem InverseMappingTheoremTasteGate_single_carrier_alignment_injective
    {x y : InverseMappingTheoremUp} :
    inverseMappingTheoremToEventFlow x = inverseMappingTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inverseMappingTheoremFromEventFlow (inverseMappingTheoremToEventFlow x) =
        inverseMappingTheoremFromEventFlow (inverseMappingTheoremToEventFlow y) :=
    congrArg inverseMappingTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (InverseMappingTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (InverseMappingTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem inverseMappingTheoremFields_faithful :
    ∀ x y : InverseMappingTheoremUp,
      inverseMappingTheoremFields x = inverseMappingTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ T₁ B₁ I₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ T₂ B₂ I₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance inverseMappingTheoremBHistCarrier :
    BHistCarrier InverseMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inverseMappingTheoremToEventFlow
  fromEventFlow := inverseMappingTheoremFromEventFlow

instance inverseMappingTheoremChapterTasteGate :
    ChapterTasteGate InverseMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inverseMappingTheoremFromEventFlow (inverseMappingTheoremToEventFlow x) = some x
    exact InverseMappingTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (InverseMappingTheoremTasteGate_single_carrier_alignment_injective heq)

instance inverseMappingTheoremFieldFaithful :
    FieldFaithful InverseMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inverseMappingTheoremFields
  field_faithful := inverseMappingTheoremFields_faithful

instance inverseMappingTheoremNontrivial : Nontrivial InverseMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InverseMappingTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InverseMappingTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def InverseMappingTheoremTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate InverseMappingTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inverseMappingTheoremChapterTasteGate

theorem InverseMappingTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inverseMappingTheoremDecodeBHist (inverseMappingTheoremEncodeBHist h) = h) ∧
      (∀ x : InverseMappingTheoremUp,
        inverseMappingTheoremFromEventFlow (inverseMappingTheoremToEventFlow x) =
          some x) ∧
      (∀ x y : InverseMappingTheoremUp,
        inverseMappingTheoremToEventFlow x = inverseMappingTheoremToEventFlow y →
          x = y) ∧
      inverseMappingTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact InverseMappingTheoremTasteGate_single_carrier_alignment_decode
  constructor
  · exact InverseMappingTheoremTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact InverseMappingTheoremTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.InverseMappingTheoremUp
