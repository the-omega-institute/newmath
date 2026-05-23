import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedDyadicCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedDyadicCauchyUp : Type where
  | mk (I B S R E H C P N : BHist) : NestedDyadicCauchyUp
  deriving DecidableEq

def nestedDyadicCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedDyadicCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedDyadicCauchyEncodeBHist h

def nestedDyadicCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedDyadicCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedDyadicCauchyDecodeBHist tail)

private theorem NestedDyadicCauchyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, nestedDyadicCauchyDecodeBHist (nestedDyadicCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedDyadicCauchyFields : NestedDyadicCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedDyadicCauchyUp.mk I B S R E H C P N => [I, B, S, R, E, H, C, P, N]

def nestedDyadicCauchyToEventFlow : NestedDyadicCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedDyadicCauchyFields x).map nestedDyadicCauchyEncodeBHist

def nestedDyadicCauchyFromEventFlow : EventFlow → Option NestedDyadicCauchyUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: restI =>
      match restI with
      | B :: restB =>
          match restB with
          | S :: restS =>
              match restS with
              | R :: restR =>
                  match restR with
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
                                            (NestedDyadicCauchyUp.mk
                                              (nestedDyadicCauchyDecodeBHist I)
                                              (nestedDyadicCauchyDecodeBHist B)
                                              (nestedDyadicCauchyDecodeBHist S)
                                              (nestedDyadicCauchyDecodeBHist R)
                                              (nestedDyadicCauchyDecodeBHist E)
                                              (nestedDyadicCauchyDecodeBHist H)
                                              (nestedDyadicCauchyDecodeBHist C)
                                              (nestedDyadicCauchyDecodeBHist P)
                                              (nestedDyadicCauchyDecodeBHist N))
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

private theorem nestedDyadicCauchy_mk_congr
    {I I' B B' S S' R R' E E' H H' C C' P P' N N' : BHist}
    (hI : I' = I) (hB : B' = B) (hS : S' = S) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    NestedDyadicCauchyUp.mk I' B' S' R' E' H' C' P' N' =
      NestedDyadicCauchyUp.mk I B S R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hB
  cases hS
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem NestedDyadicCauchyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedDyadicCauchyUp,
      nestedDyadicCauchyFromEventFlow (nestedDyadicCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B S R E H C P N =>
      exact
        congrArg some
          (nestedDyadicCauchy_mk_congr
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode I)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode B)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode S)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode R)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode E)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode H)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode C)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode P)
            (NestedDyadicCauchyTasteGate_single_carrier_alignment_decode N))

private theorem nestedDyadicCauchyToEventFlow_injective
    {x y : NestedDyadicCauchyUp} :
    nestedDyadicCauchyToEventFlow x = nestedDyadicCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedDyadicCauchyFromEventFlow (nestedDyadicCauchyToEventFlow x) =
        nestedDyadicCauchyFromEventFlow (nestedDyadicCauchyToEventFlow y) :=
    congrArg nestedDyadicCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NestedDyadicCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NestedDyadicCauchyTasteGate_single_carrier_alignment_round_trip y)))

private theorem nestedDyadicCauchy_field_faithful :
    ∀ x y : NestedDyadicCauchyUp, nestedDyadicCauchyFields x = nestedDyadicCauchyFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ B₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ B₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance nestedDyadicCauchyBHistCarrier : BHistCarrier NestedDyadicCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedDyadicCauchyToEventFlow
  fromEventFlow := nestedDyadicCauchyFromEventFlow

instance nestedDyadicCauchyChapterTasteGate : ChapterTasteGate NestedDyadicCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedDyadicCauchyFromEventFlow (nestedDyadicCauchyToEventFlow x) = some x
    exact NestedDyadicCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedDyadicCauchyToEventFlow_injective heq)

instance nestedDyadicCauchyFieldFaithful : FieldFaithful NestedDyadicCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedDyadicCauchyFields
  field_faithful := nestedDyadicCauchy_field_faithful

instance nestedDyadicCauchyNontrivial : Nontrivial NestedDyadicCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedDyadicCauchyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedDyadicCauchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedDyadicCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedDyadicCauchyChapterTasteGate

theorem NestedDyadicCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedDyadicCauchyDecodeBHist (nestedDyadicCauchyEncodeBHist h) = h) ∧
      (∀ x : NestedDyadicCauchyUp,
        nestedDyadicCauchyFromEventFlow (nestedDyadicCauchyToEventFlow x) = some x) ∧
        (∀ x y : NestedDyadicCauchyUp,
          nestedDyadicCauchyToEventFlow x = nestedDyadicCauchyToEventFlow y → x = y) ∧
          nestedDyadicCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨NestedDyadicCauchyTasteGate_single_carrier_alignment_decode,
      NestedDyadicCauchyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => nestedDyadicCauchyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NestedDyadicCauchyUp
