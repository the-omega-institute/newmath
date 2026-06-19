import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformModulusCompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformModulusCompositionUp : Type where
  | mk (X Y Z F G MF MG A T U H C P N : BHist) : CompactUniformModulusCompositionUp
  deriving DecidableEq

def compactUniformModulusCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformModulusCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformModulusCompositionEncodeBHist h

def compactUniformModulusCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformModulusCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformModulusCompositionDecodeBHist tail)

private theorem compactUniformModulusCompositionDecode_encode_bhist :
    ∀ h : BHist,
      compactUniformModulusCompositionDecodeBHist
        (compactUniformModulusCompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformModulusCompositionToEventFlow :
    CompactUniformModulusCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformModulusCompositionUp.mk X Y Z F G MF MG A T U H C P N =>
      [compactUniformModulusCompositionEncodeBHist X,
        compactUniformModulusCompositionEncodeBHist Y,
        compactUniformModulusCompositionEncodeBHist Z,
        compactUniformModulusCompositionEncodeBHist F,
        compactUniformModulusCompositionEncodeBHist G,
        compactUniformModulusCompositionEncodeBHist MF,
        compactUniformModulusCompositionEncodeBHist MG,
        compactUniformModulusCompositionEncodeBHist A,
        compactUniformModulusCompositionEncodeBHist T,
        compactUniformModulusCompositionEncodeBHist U,
        compactUniformModulusCompositionEncodeBHist H,
        compactUniformModulusCompositionEncodeBHist C,
        compactUniformModulusCompositionEncodeBHist P,
        compactUniformModulusCompositionEncodeBHist N]

def compactUniformModulusCompositionFromEventFlow :
    EventFlow → Option CompactUniformModulusCompositionUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: Y :: Z :: F :: G :: MF :: MG :: A :: T :: U :: H :: C :: P :: N :: [] =>
      some
        (CompactUniformModulusCompositionUp.mk
          (compactUniformModulusCompositionDecodeBHist X)
          (compactUniformModulusCompositionDecodeBHist Y)
          (compactUniformModulusCompositionDecodeBHist Z)
          (compactUniformModulusCompositionDecodeBHist F)
          (compactUniformModulusCompositionDecodeBHist G)
          (compactUniformModulusCompositionDecodeBHist MF)
          (compactUniformModulusCompositionDecodeBHist MG)
          (compactUniformModulusCompositionDecodeBHist A)
          (compactUniformModulusCompositionDecodeBHist T)
          (compactUniformModulusCompositionDecodeBHist U)
          (compactUniformModulusCompositionDecodeBHist H)
          (compactUniformModulusCompositionDecodeBHist C)
          (compactUniformModulusCompositionDecodeBHist P)
          (compactUniformModulusCompositionDecodeBHist N))
  | _ => none

private theorem compactUniformModulusComposition_round_trip :
    ∀ x : CompactUniformModulusCompositionUp,
      compactUniformModulusCompositionFromEventFlow
        (compactUniformModulusCompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y Z F G MF MG A T U H C P N =>
      change
        some
          (CompactUniformModulusCompositionUp.mk
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist X))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist Y))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist Z))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist F))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist G))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist MF))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist MG))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist A))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist T))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist U))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist H))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist C))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist P))
            (compactUniformModulusCompositionDecodeBHist
              (compactUniformModulusCompositionEncodeBHist N))) =
          some (CompactUniformModulusCompositionUp.mk X Y Z F G MF MG A T U H C P N)
      rw [compactUniformModulusCompositionDecode_encode_bhist X,
        compactUniformModulusCompositionDecode_encode_bhist Y,
        compactUniformModulusCompositionDecode_encode_bhist Z,
        compactUniformModulusCompositionDecode_encode_bhist F,
        compactUniformModulusCompositionDecode_encode_bhist G,
        compactUniformModulusCompositionDecode_encode_bhist MF,
        compactUniformModulusCompositionDecode_encode_bhist MG,
        compactUniformModulusCompositionDecode_encode_bhist A,
        compactUniformModulusCompositionDecode_encode_bhist T,
        compactUniformModulusCompositionDecode_encode_bhist U,
        compactUniformModulusCompositionDecode_encode_bhist H,
        compactUniformModulusCompositionDecode_encode_bhist C,
        compactUniformModulusCompositionDecode_encode_bhist P,
        compactUniformModulusCompositionDecode_encode_bhist N]

private theorem compactUniformModulusCompositionToEventFlow_injective
    {x y : CompactUniformModulusCompositionUp} :
    compactUniformModulusCompositionToEventFlow x =
      compactUniformModulusCompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformModulusCompositionFromEventFlow
          (compactUniformModulusCompositionToEventFlow x) =
        compactUniformModulusCompositionFromEventFlow
          (compactUniformModulusCompositionToEventFlow y) :=
    congrArg compactUniformModulusCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformModulusComposition_round_trip x).symm
      (Eq.trans hread (compactUniformModulusComposition_round_trip y)))

instance compactUniformModulusCompositionBHistCarrier :
    BHistCarrier CompactUniformModulusCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformModulusCompositionToEventFlow
  fromEventFlow := compactUniformModulusCompositionFromEventFlow

instance compactUniformModulusCompositionChapterTasteGate :
    ChapterTasteGate CompactUniformModulusCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformModulusCompositionFromEventFlow
        (compactUniformModulusCompositionToEventFlow x) = some x
    exact compactUniformModulusComposition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformModulusCompositionToEventFlow_injective heq)

theorem CompactUniformModulusCompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformModulusCompositionDecodeBHist
        (compactUniformModulusCompositionEncodeBHist h) = h) ∧
      (∀ x : CompactUniformModulusCompositionUp,
        compactUniformModulusCompositionFromEventFlow
          (compactUniformModulusCompositionToEventFlow x) = some x) ∧
      (∀ x y : CompactUniformModulusCompositionUp,
        compactUniformModulusCompositionToEventFlow x =
          compactUniformModulusCompositionToEventFlow y → x = y) ∧
      compactUniformModulusCompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactUniformModulusCompositionDecode_encode_bhist
  constructor
  · exact compactUniformModulusComposition_round_trip
  constructor
  · intro x y heq
    exact compactUniformModulusCompositionToEventFlow_injective heq
  · rfl

end BEDC.Derived.CompactUniformModulusCompositionUp
