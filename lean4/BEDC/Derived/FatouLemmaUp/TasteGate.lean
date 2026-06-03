import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FatouLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FatouLemmaUp : Type where
  | mk (M I A L Q R T H C P N : BHist) : FatouLemmaUp
  deriving DecidableEq

def fatouLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fatouLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fatouLemmaEncodeBHist h

def fatouLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fatouLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fatouLemmaDecodeBHist tail)

private theorem FatouLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, fatouLemmaDecodeBHist (fatouLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fatouLemmaFields : FatouLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FatouLemmaUp.mk M I A L Q R T H C P N => [M, I, A, L, Q, R, T, H, C, P, N]

def fatouLemmaToEventFlow : FatouLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fatouLemmaFields x).map fatouLemmaEncodeBHist

private def fatouLemmaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fatouLemmaEventAt index rest

def fatouLemmaFromEventFlow (ef : EventFlow) : Option FatouLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FatouLemmaUp.mk
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 0 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 1 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 2 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 3 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 4 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 5 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 6 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 7 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 8 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 9 ef))
      (fatouLemmaDecodeBHist (fatouLemmaEventAt 10 ef)))

private theorem FatouLemmaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FatouLemmaUp, fatouLemmaFromEventFlow (fatouLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M I A L Q R T H C P N =>
      change
        some
          (FatouLemmaUp.mk
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist M))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist I))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist A))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist L))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist Q))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist R))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist T))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist H))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist C))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist P))
            (fatouLemmaDecodeBHist (fatouLemmaEncodeBHist N))) =
          some (FatouLemmaUp.mk M I A L Q R T H C P N)
      rw [FatouLemmaTasteGate_single_carrier_alignment_decode_encode M,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode I,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode A,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode L,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode Q,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode R,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode T,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode H,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode C,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode P,
        FatouLemmaTasteGate_single_carrier_alignment_decode_encode N]

private theorem FatouLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FatouLemmaUp} :
    fatouLemmaToEventFlow x = fatouLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fatouLemmaFromEventFlow (fatouLemmaToEventFlow x) =
        fatouLemmaFromEventFlow (fatouLemmaToEventFlow y) :=
    congrArg fatouLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FatouLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FatouLemmaTasteGate_single_carrier_alignment_round_trip y)))

private theorem FatouLemmaTasteGate_single_carrier_alignment_fields :
    ∀ x y : FatouLemmaUp, fatouLemmaFields x = fatouLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ I₁ A₁ L₁ Q₁ R₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ I₂ A₂ L₂ Q₂ R₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance fatouLemmaBHistCarrier : BHistCarrier FatouLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fatouLemmaToEventFlow
  fromEventFlow := fatouLemmaFromEventFlow

instance fatouLemmaChapterTasteGate : ChapterTasteGate FatouLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fatouLemmaFromEventFlow (fatouLemmaToEventFlow x) = some x
    exact FatouLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FatouLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance fatouLemmaFieldFaithful : FieldFaithful FatouLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fatouLemmaFields
  field_faithful := FatouLemmaTasteGate_single_carrier_alignment_fields

instance fatouLemmaNontrivial : Nontrivial FatouLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FatouLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FatouLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FatouLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fatouLemmaChapterTasteGate

theorem FatouLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, fatouLemmaDecodeBHist (fatouLemmaEncodeBHist h) = h) ∧
      (∀ x : FatouLemmaUp, fatouLemmaFromEventFlow (fatouLemmaToEventFlow x) = some x) ∧
        (∀ x y : FatouLemmaUp, fatouLemmaToEventFlow x = fatouLemmaToEventFlow y →
          x = y) ∧
          fatouLemmaFields
              (FatouLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FatouLemmaTasteGate_single_carrier_alignment_decode_encode,
      FatouLemmaTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FatouLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FatouLemmaUp
