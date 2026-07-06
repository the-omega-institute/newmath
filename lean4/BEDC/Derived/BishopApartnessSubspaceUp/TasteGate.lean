import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopApartnessSubspaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopApartnessSubspaceUp : Type where
  | mk (X A I T H C P N : BHist) : BishopApartnessSubspaceUp
  deriving DecidableEq

def bishopApartnessSubspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopApartnessSubspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopApartnessSubspaceEncodeBHist h

def bishopApartnessSubspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopApartnessSubspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopApartnessSubspaceDecodeBHist tail)

private theorem bishopApartnessSubspaceDecode_encode_bhist :
    ∀ h : BHist,
      bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopApartnessSubspaceToEventFlow : BishopApartnessSubspaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopApartnessSubspaceUp.mk X A I T H C P N =>
      [bishopApartnessSubspaceEncodeBHist X,
        bishopApartnessSubspaceEncodeBHist A,
        bishopApartnessSubspaceEncodeBHist I,
        bishopApartnessSubspaceEncodeBHist T,
        bishopApartnessSubspaceEncodeBHist H,
        bishopApartnessSubspaceEncodeBHist C,
        bishopApartnessSubspaceEncodeBHist P,
        bishopApartnessSubspaceEncodeBHist N]

def bishopApartnessSubspaceFromEventFlow :
    EventFlow → Option BishopApartnessSubspaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [X, A, I, T, H, C, P, N] =>
      some (BishopApartnessSubspaceUp.mk
        (bishopApartnessSubspaceDecodeBHist X)
        (bishopApartnessSubspaceDecodeBHist A)
        (bishopApartnessSubspaceDecodeBHist I)
        (bishopApartnessSubspaceDecodeBHist T)
        (bishopApartnessSubspaceDecodeBHist H)
        (bishopApartnessSubspaceDecodeBHist C)
        (bishopApartnessSubspaceDecodeBHist P)
        (bishopApartnessSubspaceDecodeBHist N))
  | _ => none

private theorem bishopApartnessSubspace_round_trip :
    ∀ x : BishopApartnessSubspaceUp,
      bishopApartnessSubspaceFromEventFlow
        (bishopApartnessSubspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A I T H C P N =>
      change
        some (BishopApartnessSubspaceUp.mk
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist X))
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist A))
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist I))
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist T))
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist H))
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist C))
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist P))
          (bishopApartnessSubspaceDecodeBHist (bishopApartnessSubspaceEncodeBHist N))) =
          some (BishopApartnessSubspaceUp.mk X A I T H C P N)
      rw [bishopApartnessSubspaceDecode_encode_bhist X,
        bishopApartnessSubspaceDecode_encode_bhist A,
        bishopApartnessSubspaceDecode_encode_bhist I,
        bishopApartnessSubspaceDecode_encode_bhist T,
        bishopApartnessSubspaceDecode_encode_bhist H,
        bishopApartnessSubspaceDecode_encode_bhist C,
        bishopApartnessSubspaceDecode_encode_bhist P,
        bishopApartnessSubspaceDecode_encode_bhist N]

private theorem bishopApartnessSubspaceToEventFlow_injective
    {x y : BishopApartnessSubspaceUp} :
    bishopApartnessSubspaceToEventFlow x = bishopApartnessSubspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopApartnessSubspaceFromEventFlow (bishopApartnessSubspaceToEventFlow x) =
        bishopApartnessSubspaceFromEventFlow (bishopApartnessSubspaceToEventFlow y) :=
    congrArg bishopApartnessSubspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopApartnessSubspace_round_trip x).symm
      (Eq.trans hread (bishopApartnessSubspace_round_trip y)))

instance bishopApartnessSubspaceBHistCarrier : BHistCarrier BishopApartnessSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopApartnessSubspaceToEventFlow
  fromEventFlow := bishopApartnessSubspaceFromEventFlow

instance bishopApartnessSubspaceChapterTasteGate :
    ChapterTasteGate BishopApartnessSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopApartnessSubspaceFromEventFlow (bishopApartnessSubspaceToEventFlow x) =
      some x
    exact bishopApartnessSubspace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopApartnessSubspaceToEventFlow_injective heq)

instance bishopApartnessSubspaceFieldFaithful :
    FieldFaithful BishopApartnessSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BishopApartnessSubspaceUp.mk X A I T H C P N => [X, A, I, T, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk X₁ A₁ I₁ T₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk X₂ A₂ I₂ T₂ H₂ C₂ P₂ N₂ =>
            cases h
            rfl

instance bishopApartnessSubspaceNontrivial :
    Nontrivial BishopApartnessSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopApartnessSubspaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopApartnessSubspaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopApartnessSubspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopApartnessSubspaceChapterTasteGate

theorem BishopApartnessSubspaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopApartnessSubspaceDecodeBHist
      (bishopApartnessSubspaceEncodeBHist h) = h) ∧
      (∀ x : BishopApartnessSubspaceUp, bishopApartnessSubspaceFromEventFlow
        (bishopApartnessSubspaceToEventFlow x) = some x) ∧
        (∀ x y : BishopApartnessSubspaceUp,
          bishopApartnessSubspaceToEventFlow x =
            bishopApartnessSubspaceToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate BishopApartnessSubspaceUp) ∧
            Nonempty (FieldFaithful BishopApartnessSubspaceUp) ∧
              Nonempty (Nontrivial BishopApartnessSubspaceUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bishopApartnessSubspaceDecode_encode_bhist
  · constructor
    · exact bishopApartnessSubspace_round_trip
    · constructor
      · intro x y heq
        exact bishopApartnessSubspaceToEventFlow_injective heq
      · exact
          ⟨⟨bishopApartnessSubspaceChapterTasteGate⟩,
            ⟨bishopApartnessSubspaceFieldFaithful⟩,
            ⟨bishopApartnessSubspaceNontrivial⟩⟩

end BEDC.Derived.BishopApartnessSubspaceUp.TasteGate

namespace BEDC.Derived.BishopApartnessSubspaceUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.BishopApartnessSubspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.BishopApartnessSubspaceUp
