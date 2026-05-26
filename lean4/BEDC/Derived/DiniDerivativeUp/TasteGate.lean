import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniDerivativeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniDerivativeUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (X F Q S B R W H C P N : BHist) : DiniDerivativeUp
  deriving DecidableEq

def diniDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniDerivativeEncodeBHist h

def diniDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniDerivativeDecodeBHist tail)

private theorem DiniDerivativeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, diniDerivativeDecodeBHist (diniDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diniDerivativeFields : DiniDerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniDerivativeUp.mk X F Q S B R W H C P N => [X, F, Q, S, B, R, W, H, C, P, N]

def diniDerivativeToEventFlow : DiniDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diniDerivativeFields x).map diniDerivativeEncodeBHist

private def diniDerivativeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diniDerivativeEventAt index rest

def diniDerivativeFromEventFlow (ef : EventFlow) : Option DiniDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiniDerivativeUp.mk
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 0 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 1 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 2 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 3 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 4 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 5 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 6 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 7 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 8 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 9 ef))
      (diniDerivativeDecodeBHist (diniDerivativeEventAt 10 ef)))

private theorem DiniDerivativeTasteGate_single_carrier_alignment_round_trip
    (x : DiniDerivativeUp) :
    diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X F Q S B R W H C P N =>
      change
        some
          (DiniDerivativeUp.mk
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist X))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist F))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist Q))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist S))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist B))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist R))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist W))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist H))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist C))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist P))
            (diniDerivativeDecodeBHist (diniDerivativeEncodeBHist N))) =
          some (DiniDerivativeUp.mk X F Q S B R W H C P N)
      rw [DiniDerivativeTasteGate_single_carrier_alignment_decode_encode X,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode F,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode Q,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode S,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode B,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode R,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode W,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode H,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode C,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode P,
        DiniDerivativeTasteGate_single_carrier_alignment_decode_encode N]

private theorem DiniDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiniDerivativeUp} :
    diniDerivativeToEventFlow x = diniDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) =
        diniDerivativeFromEventFlow (diniDerivativeToEventFlow y) :=
    congrArg diniDerivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiniDerivativeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiniDerivativeTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiniDerivativeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DiniDerivativeUp, diniDerivativeFields x = diniDerivativeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ F₁ Q₁ S₁ B₁ R₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ F₂ Q₂ S₂ B₂ R₂ W₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance diniDerivativeBHistCarrier : BHistCarrier DiniDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniDerivativeToEventFlow
  fromEventFlow := diniDerivativeFromEventFlow

instance diniDerivativeChapterTasteGate : ChapterTasteGate DiniDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) = some x
    exact DiniDerivativeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiniDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance diniDerivativeFieldFaithful : FieldFaithful DiniDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diniDerivativeFields
  field_faithful := DiniDerivativeTasteGate_single_carrier_alignment_fields_faithful

instance diniDerivativeNontrivial : BEDC.Meta.TasteGate.Nontrivial DiniDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiniDerivativeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiniDerivativeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiniDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diniDerivativeChapterTasteGate

theorem DiniDerivativeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DiniDerivativeUp) ∧
      Nonempty (FieldFaithful DiniDerivativeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DiniDerivativeUp) ∧
          (∀ h : BHist, diniDerivativeDecodeBHist (diniDerivativeEncodeBHist h) = h) ∧
            (∀ x : DiniDerivativeUp,
              diniDerivativeFromEventFlow (diniDerivativeToEventFlow x) = some x) ∧
              (∀ x y : DiniDerivativeUp,
                diniDerivativeToEventFlow x = diniDerivativeToEventFlow y → x = y) ∧
                diniDerivativeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨diniDerivativeChapterTasteGate⟩,
      ⟨diniDerivativeFieldFaithful⟩,
      ⟨diniDerivativeNontrivial⟩,
      DiniDerivativeTasteGate_single_carrier_alignment_decode_encode,
      DiniDerivativeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DiniDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DiniDerivativeUp.TasteGate
