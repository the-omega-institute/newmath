import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedCauchyRealSectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedCauchyRealSectionUp : Type where
  | mk (I T W R D E H C P N : BHist) : NestedCauchyRealSectionUp
  deriving DecidableEq

def nestedCauchyRealSectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedCauchyRealSectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedCauchyRealSectionEncodeBHist h

def nestedCauchyRealSectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedCauchyRealSectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedCauchyRealSectionDecodeBHist tail)

private theorem nestedCauchyRealSectionDecode_encode :
    ∀ h : BHist,
      nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedCauchyRealSectionFields : NestedCauchyRealSectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedCauchyRealSectionUp.mk I T W R D E H C P N => [I, T, W, R, D, E, H, C, P, N]

def nestedCauchyRealSectionToEventFlow : NestedCauchyRealSectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedCauchyRealSectionFields x).map nestedCauchyRealSectionEncodeBHist

def nestedCauchyRealSectionFromEventFlow : EventFlow → Option NestedCauchyRealSectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: restI =>
      match restI with
      | T :: restT =>
          match restT with
          | W :: restW =>
              match restW with
              | R :: restR =>
                  match restR with
                  | D :: restD =>
                      match restD with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (NestedCauchyRealSectionUp.mk
                                                  (nestedCauchyRealSectionDecodeBHist I)
                                                  (nestedCauchyRealSectionDecodeBHist T)
                                                  (nestedCauchyRealSectionDecodeBHist W)
                                                  (nestedCauchyRealSectionDecodeBHist R)
                                                  (nestedCauchyRealSectionDecodeBHist D)
                                                  (nestedCauchyRealSectionDecodeBHist E)
                                                  (nestedCauchyRealSectionDecodeBHist H)
                                                  (nestedCauchyRealSectionDecodeBHist C)
                                                  (nestedCauchyRealSectionDecodeBHist P)
                                                  (nestedCauchyRealSectionDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem nestedCauchyRealSection_round_trip :
    ∀ x : NestedCauchyRealSectionUp,
      nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I T W R D E H C P N =>
      change
        some
          (NestedCauchyRealSectionUp.mk
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist I))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist T))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist W))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist R))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist D))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist E))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist H))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist C))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist P))
            (nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist N))) =
          some (NestedCauchyRealSectionUp.mk I T W R D E H C P N)
      rw [nestedCauchyRealSectionDecode_encode I, nestedCauchyRealSectionDecode_encode T,
        nestedCauchyRealSectionDecode_encode W, nestedCauchyRealSectionDecode_encode R,
        nestedCauchyRealSectionDecode_encode D, nestedCauchyRealSectionDecode_encode E,
        nestedCauchyRealSectionDecode_encode H, nestedCauchyRealSectionDecode_encode C,
        nestedCauchyRealSectionDecode_encode P, nestedCauchyRealSectionDecode_encode N]

private theorem nestedCauchyRealSectionToEventFlow_injective
    {x y : NestedCauchyRealSectionUp} :
    nestedCauchyRealSectionToEventFlow x = nestedCauchyRealSectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow x) =
        nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow y) :=
    congrArg nestedCauchyRealSectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedCauchyRealSection_round_trip x).symm
      (Eq.trans hread (nestedCauchyRealSection_round_trip y)))

private theorem nestedCauchyRealSection_field_faithful :
    ∀ x y : NestedCauchyRealSectionUp,
      nestedCauchyRealSectionFields x = nestedCauchyRealSectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ T₁ W₁ R₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ T₂ W₂ R₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance nestedCauchyRealSectionBHistCarrier :
    BHistCarrier NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedCauchyRealSectionToEventFlow
  fromEventFlow := nestedCauchyRealSectionFromEventFlow

instance nestedCauchyRealSectionChapterTasteGate :
    ChapterTasteGate NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow x) = some x
    exact nestedCauchyRealSection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedCauchyRealSectionToEventFlow_injective heq)

instance nestedCauchyRealSectionFieldFaithful :
    FieldFaithful NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedCauchyRealSectionFields
  field_faithful := nestedCauchyRealSection_field_faithful

instance nestedCauchyRealSectionNontrivial :
    Nontrivial NestedCauchyRealSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedCauchyRealSectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedCauchyRealSectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedCauchyRealSectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedCauchyRealSectionChapterTasteGate

theorem NestedCauchyRealSectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedCauchyRealSectionDecodeBHist (nestedCauchyRealSectionEncodeBHist h) = h) ∧
      (∀ x : NestedCauchyRealSectionUp,
        nestedCauchyRealSectionFromEventFlow (nestedCauchyRealSectionToEventFlow x) = some x) ∧
        (∀ x y : NestedCauchyRealSectionUp,
          nestedCauchyRealSectionToEventFlow x = nestedCauchyRealSectionToEventFlow y → x = y) ∧
          nestedCauchyRealSectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨nestedCauchyRealSectionDecode_encode, nestedCauchyRealSection_round_trip,
      (fun _ _ heq => nestedCauchyRealSectionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.NestedCauchyRealSectionUp
