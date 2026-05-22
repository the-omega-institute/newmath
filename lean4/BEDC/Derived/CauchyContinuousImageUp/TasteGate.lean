import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuousImageUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContinuousImageUp : Type where
  | mk (S R D M J E H C P N : BHist) : CauchyContinuousImageUp
  deriving DecidableEq

def cauchyContinuousImageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuousImageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuousImageEncodeBHist h

def cauchyContinuousImageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuousImageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuousImageDecodeBHist tail)

private theorem CauchyContinuousImageTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyContinuousImageDecodeBHist (cauchyContinuousImageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContinuousImageFields : CauchyContinuousImageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuousImageUp.mk S R D M J E H C P N => [S, R, D, M, J, E, H, C, P, N]

def cauchyContinuousImageToEventFlow : CauchyContinuousImageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyContinuousImageFields x).map cauchyContinuousImageEncodeBHist

def cauchyContinuousImageFromEventFlow : EventFlow → Option CauchyContinuousImageUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | R :: restR =>
          match restR with
          | D :: restD =>
              match restD with
              | M :: restM =>
                  match restM with
                  | J :: restJ =>
                      match restJ with
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
                                                (CauchyContinuousImageUp.mk
                                                  (cauchyContinuousImageDecodeBHist S)
                                                  (cauchyContinuousImageDecodeBHist R)
                                                  (cauchyContinuousImageDecodeBHist D)
                                                  (cauchyContinuousImageDecodeBHist M)
                                                  (cauchyContinuousImageDecodeBHist J)
                                                  (cauchyContinuousImageDecodeBHist E)
                                                  (cauchyContinuousImageDecodeBHist H)
                                                  (cauchyContinuousImageDecodeBHist C)
                                                  (cauchyContinuousImageDecodeBHist P)
                                                  (cauchyContinuousImageDecodeBHist N))
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

private theorem cauchyContinuousImage_mk_congr
    {S S' R R' D D' M M' J J' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hR : R' = R) (hD : D' = D) (hM : M' = M)
    (hJ : J' = J) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyContinuousImageUp.mk S' R' D' M' J' E' H' C' P' N' =
      CauchyContinuousImageUp.mk S R D M J E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hR
  cases hD
  cases hM
  cases hJ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyContinuousImageTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyContinuousImageUp,
      cauchyContinuousImageFromEventFlow (cauchyContinuousImageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D M J E H C P N =>
      exact
        congrArg some
          (cauchyContinuousImage_mk_congr
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode S)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode R)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode D)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode M)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode J)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode E)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode H)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode C)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode P)
            (CauchyContinuousImageTasteGate_single_carrier_alignment_decode N))

private theorem cauchyContinuousImageToEventFlow_injective
    {x y : CauchyContinuousImageUp} :
    cauchyContinuousImageToEventFlow x = cauchyContinuousImageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuousImageFromEventFlow (cauchyContinuousImageToEventFlow x) =
        cauchyContinuousImageFromEventFlow (cauchyContinuousImageToEventFlow y) :=
    congrArg cauchyContinuousImageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyContinuousImageTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyContinuousImageTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyContinuousImage_field_faithful :
    ∀ x y : CauchyContinuousImageUp,
      cauchyContinuousImageFields x = cauchyContinuousImageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S R D M J E H C P N =>
      cases y with
      | mk S' R' D' M' J' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyContinuousImageBHistCarrier : BHistCarrier CauchyContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuousImageToEventFlow
  fromEventFlow := cauchyContinuousImageFromEventFlow

instance cauchyContinuousImageChapterTasteGate :
    ChapterTasteGate CauchyContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyContinuousImageFromEventFlow (cauchyContinuousImageToEventFlow x) = some x
    exact CauchyContinuousImageTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyContinuousImageToEventFlow_injective heq)

instance cauchyContinuousImageFieldFaithful :
    FieldFaithful CauchyContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyContinuousImageFields
  field_faithful := cauchyContinuousImage_field_faithful

instance cauchyContinuousImageNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyContinuousImageUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyContinuousImageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyContinuousImageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyContinuousImageChapterTasteGate

theorem CauchyContinuousImageTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyContinuousImageUp) ∧
      Nonempty (FieldFaithful CauchyContinuousImageUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyContinuousImageUp) ∧
      (∀ h : BHist, cauchyContinuousImageDecodeBHist (cauchyContinuousImageEncodeBHist h) = h) ∧
      (∀ x : CauchyContinuousImageUp,
        cauchyContinuousImageFromEventFlow (cauchyContinuousImageToEventFlow x) = some x) ∧
      (∀ x y : CauchyContinuousImageUp,
        cauchyContinuousImageToEventFlow x = cauchyContinuousImageToEventFlow y → x = y) ∧
      cauchyContinuousImageEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyContinuousImageChapterTasteGate⟩
  constructor
  · exact ⟨cauchyContinuousImageFieldFaithful⟩
  constructor
  · exact ⟨cauchyContinuousImageNontrivial⟩
  constructor
  · exact CauchyContinuousImageTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyContinuousImageTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyContinuousImageToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.CauchyContinuousImageUp
