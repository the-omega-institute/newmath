import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrimitiveDistinctionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrimitiveDistinctionLedgerUp : Type where
  | mk : (Z O D T R H C P N : BHist) → PrimitiveDistinctionLedgerUp
  deriving DecidableEq

private def primitiveDistinctionLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: primitiveDistinctionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: primitiveDistinctionLedgerEncodeBHist h

private def primitiveDistinctionLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (primitiveDistinctionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (primitiveDistinctionLedgerDecodeBHist tail)

private theorem primitiveDistinctionLedgerDecode_encode_bhist :
    ∀ h : BHist,
      primitiveDistinctionLedgerDecodeBHist
        (primitiveDistinctionLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def primitiveDistinctionLedgerToEventFlow :
    PrimitiveDistinctionLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N =>
      [[BMark.b0],
        primitiveDistinctionLedgerEncodeBHist Z,
        [BMark.b1, BMark.b0],
        primitiveDistinctionLedgerEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b0],
        primitiveDistinctionLedgerEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        primitiveDistinctionLedgerEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        primitiveDistinctionLedgerEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        primitiveDistinctionLedgerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        primitiveDistinctionLedgerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        primitiveDistinctionLedgerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        primitiveDistinctionLedgerEncodeBHist N]

private def primitiveDistinctionLedgerFromEventFlow :
    EventFlow → Option PrimitiveDistinctionLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, Z, _tag1, O, _tag2, D, _tag3, T, _tag4, R, _tag5, H, _tag6, C,
      _tag7, P, _tag8, N] =>
      some
        (PrimitiveDistinctionLedgerUp.mk
          (primitiveDistinctionLedgerDecodeBHist Z)
          (primitiveDistinctionLedgerDecodeBHist O)
          (primitiveDistinctionLedgerDecodeBHist D)
          (primitiveDistinctionLedgerDecodeBHist T)
          (primitiveDistinctionLedgerDecodeBHist R)
          (primitiveDistinctionLedgerDecodeBHist H)
          (primitiveDistinctionLedgerDecodeBHist C)
          (primitiveDistinctionLedgerDecodeBHist P)
          (primitiveDistinctionLedgerDecodeBHist N))
  | _ => none

private theorem primitiveDistinctionLedger_round_trip :
    ∀ x : PrimitiveDistinctionLedgerUp,
      primitiveDistinctionLedgerFromEventFlow
        (primitiveDistinctionLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Z O D T R H C P N =>
      change
        some
          (PrimitiveDistinctionLedgerUp.mk
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist Z))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist O))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist D))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist T))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist R))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist H))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist C))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist P))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist N))) =
          some (PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N)
      rw [primitiveDistinctionLedgerDecode_encode_bhist Z,
        primitiveDistinctionLedgerDecode_encode_bhist O,
        primitiveDistinctionLedgerDecode_encode_bhist D,
        primitiveDistinctionLedgerDecode_encode_bhist T,
        primitiveDistinctionLedgerDecode_encode_bhist R,
        primitiveDistinctionLedgerDecode_encode_bhist H,
        primitiveDistinctionLedgerDecode_encode_bhist C,
        primitiveDistinctionLedgerDecode_encode_bhist P,
        primitiveDistinctionLedgerDecode_encode_bhist N]

private theorem primitiveDistinctionLedgerToEventFlow_injective
    {x y : PrimitiveDistinctionLedgerUp} :
    primitiveDistinctionLedgerToEventFlow x =
      primitiveDistinctionLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      primitiveDistinctionLedgerFromEventFlow
          (primitiveDistinctionLedgerToEventFlow x) =
        primitiveDistinctionLedgerFromEventFlow
          (primitiveDistinctionLedgerToEventFlow y) :=
    congrArg primitiveDistinctionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (primitiveDistinctionLedger_round_trip x).symm
      (Eq.trans hread (primitiveDistinctionLedger_round_trip y)))

instance primitiveDistinctionLedgerBHistCarrier :
    BHistCarrier PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := primitiveDistinctionLedgerToEventFlow
  fromEventFlow := primitiveDistinctionLedgerFromEventFlow

instance primitiveDistinctionLedgerChapterTasteGate :
    ChapterTasteGate PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      primitiveDistinctionLedgerFromEventFlow
        (primitiveDistinctionLedgerToEventFlow x) = some x
    exact primitiveDistinctionLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (primitiveDistinctionLedgerToEventFlow_injective heq)

instance primitiveDistinctionLedgerFieldFaithful :
    FieldFaithful PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N => [Z, O, D, T, R, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk Z₁ O₁ D₁ T₁ R₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk Z₂ O₂ D₂ T₂ R₂ H₂ C₂ P₂ N₂ =>
            simp only [] at h
            cases h
            rfl

instance primitiveDistinctionLedgerNontrivial :
    Nontrivial PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PrimitiveDistinctionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PrimitiveDistinctionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PrimitiveDistinctionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  primitiveDistinctionLedgerChapterTasteGate

end BEDC.Derived.PrimitiveDistinctionLedgerUp
