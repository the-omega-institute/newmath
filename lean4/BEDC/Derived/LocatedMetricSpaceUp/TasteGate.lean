import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedMetricSpaceUp : Type where
  | mk (X M D R E H C P N : BHist) : LocatedMetricSpaceUp
  deriving DecidableEq

def locatedMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedMetricSpaceEncodeBHist h

def locatedMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedMetricSpaceDecodeBHist tail)

private theorem locatedMetricSpaceDecodeEncode :
    ∀ h : BHist, locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedMetricSpaceFields : LocatedMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedMetricSpaceUp.mk X M D R E H C P N => [X, M, D, R, E, H, C, P, N]

def locatedMetricSpaceToEventFlow : LocatedMetricSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedMetricSpaceFields x).map locatedMetricSpaceEncodeBHist

private def locatedMetricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedMetricSpaceEventAtDefault index rest

def locatedMetricSpaceFromEventFlow (ef : EventFlow) : Option LocatedMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedMetricSpaceUp.mk
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 0 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 1 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 2 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 3 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 4 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 5 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 6 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 7 ef))
      (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEventAtDefault 8 ef)))

private theorem locatedMetricSpaceRoundTrip :
    ∀ x : LocatedMetricSpaceUp,
      locatedMetricSpaceFromEventFlow (locatedMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M D R E H C P N =>
      change
        some
          (LocatedMetricSpaceUp.mk
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist X))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist M))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist D))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist R))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist E))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist H))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist C))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist P))
            (locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist N))) =
          some (LocatedMetricSpaceUp.mk X M D R E H C P N)
      rw [locatedMetricSpaceDecodeEncode X, locatedMetricSpaceDecodeEncode M,
        locatedMetricSpaceDecodeEncode D, locatedMetricSpaceDecodeEncode R,
        locatedMetricSpaceDecodeEncode E, locatedMetricSpaceDecodeEncode H,
        locatedMetricSpaceDecodeEncode C, locatedMetricSpaceDecodeEncode P,
        locatedMetricSpaceDecodeEncode N]

private theorem locatedMetricSpaceToEventFlow_injective
    {x y : LocatedMetricSpaceUp} :
    locatedMetricSpaceToEventFlow x = locatedMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedMetricSpaceFromEventFlow (locatedMetricSpaceToEventFlow x) =
        locatedMetricSpaceFromEventFlow (locatedMetricSpaceToEventFlow y) :=
    congrArg locatedMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedMetricSpaceRoundTrip x).symm
      (Eq.trans hread (locatedMetricSpaceRoundTrip y)))

private theorem locatedMetricSpaceFieldFaithfulProof :
    ∀ x y : LocatedMetricSpaceUp,
      locatedMetricSpaceFields x = locatedMetricSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X₁ M₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ M₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          change [X₁, M₁, D₁, R₁, E₁, H₁, C₁, P₁, N₁] =
            [X₂, M₂, D₂, R₂, E₂, H₂, C₂, P₂, N₂] at h
          cases h
          rfl

instance locatedMetricSpaceBHistCarrier : BHistCarrier LocatedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedMetricSpaceToEventFlow
  fromEventFlow := locatedMetricSpaceFromEventFlow

instance locatedMetricSpaceChapterTasteGate : ChapterTasteGate LocatedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedMetricSpaceFromEventFlow (locatedMetricSpaceToEventFlow x) = some x
    exact locatedMetricSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedMetricSpaceToEventFlow_injective heq)

instance locatedMetricSpaceFieldFaithful : FieldFaithful LocatedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedMetricSpaceFields
  field_faithful := locatedMetricSpaceFieldFaithfulProof

theorem LocatedMetricSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedMetricSpaceDecodeBHist (locatedMetricSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedMetricSpaceUp) ∧
        Nonempty (ChapterTasteGate LocatedMetricSpaceUp) ∧
          locatedMetricSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨locatedMetricSpaceDecodeEncode,
      ⟨locatedMetricSpaceBHistCarrier⟩,
      ⟨locatedMetricSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedMetricSpaceUp
