import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConfluenceDiamondBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConfluenceDiamondBoundaryUp : Type where
  | mk (K J R S B O H C P N : BHist) : MetaCICConfluenceDiamondBoundaryUp
  deriving DecidableEq

def metaCICConfluenceDiamondBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConfluenceDiamondBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConfluenceDiamondBoundaryEncodeBHist h

def metaCICConfluenceDiamondBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConfluenceDiamondBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConfluenceDiamondBoundaryDecodeBHist tail)

private theorem metaCICConfluenceDiamondBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      metaCICConfluenceDiamondBoundaryDecodeBHist
        (metaCICConfluenceDiamondBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICConfluenceDiamondBoundaryFields :
    MetaCICConfluenceDiamondBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceDiamondBoundaryUp.mk K J R S B O H C P N =>
      [K, J, R, S, B, O, H, C, P, N]

def metaCICConfluenceDiamondBoundaryToEventFlow :
    MetaCICConfluenceDiamondBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICConfluenceDiamondBoundaryFields x).map
      metaCICConfluenceDiamondBoundaryEncodeBHist

def metaCICConfluenceDiamondBoundaryFromEventFlow :
    EventFlow → Option MetaCICConfluenceDiamondBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: J :: R :: S :: B :: O :: H :: C :: P :: N :: [] =>
      some
        (MetaCICConfluenceDiamondBoundaryUp.mk
          (metaCICConfluenceDiamondBoundaryDecodeBHist K)
          (metaCICConfluenceDiamondBoundaryDecodeBHist J)
          (metaCICConfluenceDiamondBoundaryDecodeBHist R)
          (metaCICConfluenceDiamondBoundaryDecodeBHist S)
          (metaCICConfluenceDiamondBoundaryDecodeBHist B)
          (metaCICConfluenceDiamondBoundaryDecodeBHist O)
          (metaCICConfluenceDiamondBoundaryDecodeBHist H)
          (metaCICConfluenceDiamondBoundaryDecodeBHist C)
          (metaCICConfluenceDiamondBoundaryDecodeBHist P)
          (metaCICConfluenceDiamondBoundaryDecodeBHist N))
  | _ => none

private theorem metaCICConfluenceDiamondBoundary_round_trip :
    ∀ x : MetaCICConfluenceDiamondBoundaryUp,
      metaCICConfluenceDiamondBoundaryFromEventFlow
        (metaCICConfluenceDiamondBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K J R S B O H C P N =>
      change
        some
            (MetaCICConfluenceDiamondBoundaryUp.mk
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist K))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist J))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist R))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist S))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist B))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist O))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist H))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist C))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist P))
              (metaCICConfluenceDiamondBoundaryDecodeBHist
                (metaCICConfluenceDiamondBoundaryEncodeBHist N))) =
          some (MetaCICConfluenceDiamondBoundaryUp.mk K J R S B O H C P N)
      rw [metaCICConfluenceDiamondBoundaryDecode_encode_bhist K,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist J,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist R,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist S,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist B,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist O,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist H,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist C,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist P,
        metaCICConfluenceDiamondBoundaryDecode_encode_bhist N]

private theorem metaCICConfluenceDiamondBoundaryToEventFlow_injective
    {x y : MetaCICConfluenceDiamondBoundaryUp} :
    metaCICConfluenceDiamondBoundaryToEventFlow x =
      metaCICConfluenceDiamondBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConfluenceDiamondBoundaryFromEventFlow
          (metaCICConfluenceDiamondBoundaryToEventFlow x) =
        metaCICConfluenceDiamondBoundaryFromEventFlow
          (metaCICConfluenceDiamondBoundaryToEventFlow y) :=
    congrArg metaCICConfluenceDiamondBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICConfluenceDiamondBoundary_round_trip x).symm
      (Eq.trans hread (metaCICConfluenceDiamondBoundary_round_trip y)))

private theorem metaCICConfluenceDiamondBoundary_fields_faithful :
    ∀ x y : MetaCICConfluenceDiamondBoundaryUp,
      metaCICConfluenceDiamondBoundaryFields x =
        metaCICConfluenceDiamondBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K J R S B O H C P N =>
      cases y with
      | mk K' J' R' S' B' O' H' C' P' N' =>
          cases hfields
          rfl

instance metaCICConfluenceDiamondBoundaryBHistCarrier :
    BHistCarrier MetaCICConfluenceDiamondBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConfluenceDiamondBoundaryToEventFlow
  fromEventFlow := metaCICConfluenceDiamondBoundaryFromEventFlow

instance metaCICConfluenceDiamondBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICConfluenceDiamondBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := metaCICConfluenceDiamondBoundary_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICConfluenceDiamondBoundaryToEventFlow_injective heq)

instance metaCICConfluenceDiamondBoundaryFieldFaithful :
    FieldFaithful MetaCICConfluenceDiamondBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICConfluenceDiamondBoundaryFields
  field_faithful := metaCICConfluenceDiamondBoundary_fields_faithful

instance metaCICConfluenceDiamondBoundaryNontrivial :
    Nontrivial MetaCICConfluenceDiamondBoundaryUp where
  witness_pair :=
    ⟨MetaCICConfluenceDiamondBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICConfluenceDiamondBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICConfluenceDiamondBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConfluenceDiamondBoundaryChapterTasteGate

end BEDC.Derived.MetaCICConfluenceDiamondBoundaryUp
