import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyWindowIntersectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyWindowIntersectionUp : Type where
  | mk (X Y WX WY D M T H C P N : BHist) : RegularCauchyWindowIntersectionUp
  deriving DecidableEq

private def regularCauchyWindowIntersectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyWindowIntersectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyWindowIntersectionEncodeBHist h

private def regularCauchyWindowIntersectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyWindowIntersectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyWindowIntersectionDecodeBHist tail)

private theorem regularCauchyWindowIntersection_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyWindowIntersectionDecodeBHist
        (regularCauchyWindowIntersectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def regularCauchyWindowIntersectionToEventFlow :
    RegularCauchyWindowIntersectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyWindowIntersectionUp.mk X Y WX WY D M T H C P N =>
      [[BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist X,
        [BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist WX,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist WY,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowIntersectionEncodeBHist N]

private def regularCauchyWindowIntersectionFromEventFlow :
    EventFlow → Option RegularCauchyWindowIntersectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, X, _tag1, Y, _tag2, WX, _tag3, WY, _tag4, D, _tag5, M, _tag6, T,
      _tag7, H, _tag8, C, _tag9, P, _tag10, N] =>
      some
        (RegularCauchyWindowIntersectionUp.mk
          (regularCauchyWindowIntersectionDecodeBHist X)
          (regularCauchyWindowIntersectionDecodeBHist Y)
          (regularCauchyWindowIntersectionDecodeBHist WX)
          (regularCauchyWindowIntersectionDecodeBHist WY)
          (regularCauchyWindowIntersectionDecodeBHist D)
          (regularCauchyWindowIntersectionDecodeBHist M)
          (regularCauchyWindowIntersectionDecodeBHist T)
          (regularCauchyWindowIntersectionDecodeBHist H)
          (regularCauchyWindowIntersectionDecodeBHist C)
          (regularCauchyWindowIntersectionDecodeBHist P)
          (regularCauchyWindowIntersectionDecodeBHist N))
  | _ => none

private theorem regularCauchyWindowIntersection_round_trip :
    ∀ x : RegularCauchyWindowIntersectionUp,
      regularCauchyWindowIntersectionFromEventFlow
        (regularCauchyWindowIntersectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y WX WY D M T H C P N =>
      change
        some
          (RegularCauchyWindowIntersectionUp.mk
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist X))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist Y))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist WX))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist WY))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist D))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist M))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist T))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist H))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist C))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist P))
            (regularCauchyWindowIntersectionDecodeBHist
              (regularCauchyWindowIntersectionEncodeBHist N))) =
          some (RegularCauchyWindowIntersectionUp.mk X Y WX WY D M T H C P N)
      rw [regularCauchyWindowIntersection_decode_encode_bhist X,
        regularCauchyWindowIntersection_decode_encode_bhist Y,
        regularCauchyWindowIntersection_decode_encode_bhist WX,
        regularCauchyWindowIntersection_decode_encode_bhist WY,
        regularCauchyWindowIntersection_decode_encode_bhist D,
        regularCauchyWindowIntersection_decode_encode_bhist M,
        regularCauchyWindowIntersection_decode_encode_bhist T,
        regularCauchyWindowIntersection_decode_encode_bhist H,
        regularCauchyWindowIntersection_decode_encode_bhist C,
        regularCauchyWindowIntersection_decode_encode_bhist P,
        regularCauchyWindowIntersection_decode_encode_bhist N]

private theorem regularCauchyWindowIntersectionToEventFlow_injective
    {x y : RegularCauchyWindowIntersectionUp} :
    regularCauchyWindowIntersectionToEventFlow x =
      regularCauchyWindowIntersectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyWindowIntersectionFromEventFlow
          (regularCauchyWindowIntersectionToEventFlow x) =
        regularCauchyWindowIntersectionFromEventFlow
          (regularCauchyWindowIntersectionToEventFlow y) :=
    congrArg regularCauchyWindowIntersectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyWindowIntersection_round_trip x).symm
      (Eq.trans hread (regularCauchyWindowIntersection_round_trip y)))

private def regularCauchyWindowIntersectionFields :
    RegularCauchyWindowIntersectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyWindowIntersectionUp.mk X Y WX WY D M T H C P N =>
      [X, Y, WX, WY, D, M, T, H, C, P, N]

private theorem regularCauchyWindowIntersection_fields_faithful :
    ∀ x y : RegularCauchyWindowIntersectionUp,
      regularCauchyWindowIntersectionFields x =
        regularCauchyWindowIntersectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ WX₁ WY₁ D₁ M₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ WX₂ WY₂ D₂ M₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyWindowIntersectionBHistCarrier :
    BHistCarrier RegularCauchyWindowIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyWindowIntersectionToEventFlow
  fromEventFlow := regularCauchyWindowIntersectionFromEventFlow

instance regularCauchyWindowIntersectionChapterTasteGate :
    ChapterTasteGate RegularCauchyWindowIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyWindowIntersectionFromEventFlow
        (regularCauchyWindowIntersectionToEventFlow x) = some x
    exact regularCauchyWindowIntersection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyWindowIntersectionToEventFlow_injective heq)

instance regularCauchyWindowIntersectionFieldFaithful :
    FieldFaithful RegularCauchyWindowIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyWindowIntersectionFields
  field_faithful := regularCauchyWindowIntersection_fields_faithful

instance regularCauchyWindowIntersectionNontrivial :
    Nontrivial RegularCauchyWindowIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyWindowIntersectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyWindowIntersectionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyWindowIntersectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyWindowIntersectionChapterTasteGate

end BEDC.Derived.RegularCauchyWindowIntersectionUp
