import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopMetricSpaceUp : Type where
  | mk (X D S R A H C P N : BHist) : BishopMetricSpaceUp
  deriving DecidableEq

def bishopMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopMetricSpaceEncodeBHist h

def bishopMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopMetricSpaceDecodeBHist tail)

private theorem bishopMetricSpaceDecodeEncode :
    ∀ h : BHist, bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopMetricSpaceToEventFlow : BishopMetricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopMetricSpaceUp.mk X D S R A H C P N =>
      [[BMark.b0],
        bishopMetricSpaceEncodeBHist X,
        [BMark.b1, BMark.b0],
        bishopMetricSpaceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        bishopMetricSpaceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopMetricSpaceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopMetricSpaceEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopMetricSpaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopMetricSpaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopMetricSpaceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bishopMetricSpaceEncodeBHist N]

private def bishopMetricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopMetricSpaceEventAtDefault index rest

def bishopMetricSpaceFromEventFlow (ef : EventFlow) : Option BishopMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopMetricSpaceUp.mk
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 1 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 3 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 5 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 7 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 9 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 11 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 13 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 15 ef))
      (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEventAtDefault 17 ef)))

private theorem bishopMetricSpaceRoundTrip :
    ∀ x : BishopMetricSpaceUp,
      bishopMetricSpaceFromEventFlow (bishopMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X D S R A H C P N =>
      change
        some
          (BishopMetricSpaceUp.mk
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist X))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist D))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist S))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist R))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist A))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist H))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist C))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist P))
            (bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist N))) =
          some (BishopMetricSpaceUp.mk X D S R A H C P N)
      rw [bishopMetricSpaceDecodeEncode X, bishopMetricSpaceDecodeEncode D,
        bishopMetricSpaceDecodeEncode S, bishopMetricSpaceDecodeEncode R,
        bishopMetricSpaceDecodeEncode A, bishopMetricSpaceDecodeEncode H,
        bishopMetricSpaceDecodeEncode C, bishopMetricSpaceDecodeEncode P,
        bishopMetricSpaceDecodeEncode N]

private theorem bishopMetricSpaceToEventFlow_injective {x y : BishopMetricSpaceUp} :
    bishopMetricSpaceToEventFlow x = bishopMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopMetricSpaceFromEventFlow (bishopMetricSpaceToEventFlow x) =
        bishopMetricSpaceFromEventFlow (bishopMetricSpaceToEventFlow y) :=
    congrArg bishopMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopMetricSpaceRoundTrip x).symm
      (Eq.trans hread (bishopMetricSpaceRoundTrip y)))

def bishopMetricSpaceFields : BishopMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopMetricSpaceUp.mk X D S R A H C P N => [X, D, S, R, A, H, C, P, N]

instance bishopMetricSpaceBHistCarrier : BHistCarrier BishopMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopMetricSpaceToEventFlow
  fromEventFlow := bishopMetricSpaceFromEventFlow

instance bishopMetricSpaceChapterTasteGate : ChapterTasteGate BishopMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopMetricSpaceFromEventFlow (bishopMetricSpaceToEventFlow x) = some x
    exact bishopMetricSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopMetricSpaceToEventFlow_injective heq)

instance bishopMetricSpaceFieldFaithful : FieldFaithful BishopMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopMetricSpaceFields
  field_faithful := by
    intro x y h
    cases x with
    | mk X₁ D₁ S₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ D₂ S₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
        change [X₁, D₁, S₁, R₁, A₁, H₁, C₁, P₁, N₁] =
          [X₂, D₂, S₂, R₂, A₂, H₂, C₂, P₂, N₂] at h
        cases h
        rfl

instance bishopMetricSpaceNontrivial : Nontrivial BishopMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopMetricSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopMetricSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopMetricSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopMetricSpaceDecodeBHist (bishopMetricSpaceEncodeBHist h) = h) ∧
      (∀ x : BishopMetricSpaceUp,
        bishopMetricSpaceFromEventFlow (bishopMetricSpaceToEventFlow x) = some x) ∧
        (∀ x y : BishopMetricSpaceUp,
          bishopMetricSpaceToEventFlow x = bishopMetricSpaceToEventFlow y → x = y) ∧
          bishopMetricSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨bishopMetricSpaceDecodeEncode,
      bishopMetricSpaceRoundTrip,
      fun _ _ heq => bishopMetricSpaceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BishopMetricSpaceUp
