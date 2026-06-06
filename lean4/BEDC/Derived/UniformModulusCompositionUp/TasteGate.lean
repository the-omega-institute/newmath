import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformModulusCompositionUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformModulusCompositionUp : Type where
  | mk (F G MF MG B W D R E H C P N : BHist) : UniformModulusCompositionUp
  deriving DecidableEq

def uniformModulusCompositionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformModulusCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformModulusCompositionEncodeBHist h

def uniformModulusCompositionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformModulusCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformModulusCompositionDecodeBHist tail)

private theorem UniformModulusCompositionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      uniformModulusCompositionDecodeBHist (uniformModulusCompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformModulusCompositionFields : UniformModulusCompositionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformModulusCompositionUp.mk F G MF MG B W D R E H C P N =>
      [F, G, MF, MG, B, W, D, R, E, H, C, P, N]

def uniformModulusCompositionToEventFlow : UniformModulusCompositionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformModulusCompositionFields x).map uniformModulusCompositionEncodeBHist

def uniformModulusCompositionFromEventFlow : EventFlow -> Option UniformModulusCompositionUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | G :: restG =>
          match restG with
          | MF :: restMF =>
              match restMF with
              | MG :: restMG =>
                  match restMG with
                  | B :: restB =>
                      match restB with
                      | W :: restW =>
                          match restW with
                          | D :: restD =>
                              match restD with
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
                                                  | N :: rest =>
                                                      match rest with
                                                      | [] =>
                                                          some
                                                            (UniformModulusCompositionUp.mk
                                                              (uniformModulusCompositionDecodeBHist F)
                                                              (uniformModulusCompositionDecodeBHist G)
                                                              (uniformModulusCompositionDecodeBHist MF)
                                                              (uniformModulusCompositionDecodeBHist MG)
                                                              (uniformModulusCompositionDecodeBHist B)
                                                              (uniformModulusCompositionDecodeBHist W)
                                                              (uniformModulusCompositionDecodeBHist D)
                                                              (uniformModulusCompositionDecodeBHist R)
                                                              (uniformModulusCompositionDecodeBHist E)
                                                              (uniformModulusCompositionDecodeBHist H)
                                                              (uniformModulusCompositionDecodeBHist C)
                                                              (uniformModulusCompositionDecodeBHist P)
                                                              (uniformModulusCompositionDecodeBHist N))
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
          | [] => none
      | [] => none
  | [] => none

private theorem uniformModulusComposition_mk_congr
    {F F' G G' MF MF' MG MG' B B' W W' D D' R R' E E' H H' C C' P P' N N' :
      BHist}
    (hF : F' = F) (hG : G' = G) (hMF : MF' = MF) (hMG : MG' = MG)
    (hB : B' = B) (hW : W' = W) (hD : D' = D) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    UniformModulusCompositionUp.mk F' G' MF' MG' B' W' D' R' E' H' C' P' N' =
      UniformModulusCompositionUp.mk F G MF MG B W D R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hG
  cases hMF
  cases hMG
  cases hB
  cases hW
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem UniformModulusCompositionTasteGate_single_carrier_alignment_round_trip :
    forall x : UniformModulusCompositionUp,
      uniformModulusCompositionFromEventFlow (uniformModulusCompositionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G MF MG B W D R E H C P N =>
      exact
        congrArg some
          (uniformModulusComposition_mk_congr
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode F)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode G)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode MF)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode MG)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode B)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode W)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode D)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode R)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode E)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode H)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode C)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode P)
            (UniformModulusCompositionTasteGate_single_carrier_alignment_decode N))

private theorem uniformModulusCompositionToEventFlow_injective
    {x y : UniformModulusCompositionUp} :
    uniformModulusCompositionToEventFlow x = uniformModulusCompositionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformModulusCompositionFromEventFlow (uniformModulusCompositionToEventFlow x) =
        uniformModulusCompositionFromEventFlow (uniformModulusCompositionToEventFlow y) :=
    congrArg uniformModulusCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformModulusCompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformModulusCompositionTasteGate_single_carrier_alignment_round_trip y)))

instance uniformModulusCompositionBHistCarrier :
    BHistCarrier UniformModulusCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformModulusCompositionToEventFlow
  fromEventFlow := uniformModulusCompositionFromEventFlow

instance uniformModulusCompositionChapterTasteGate :
    ChapterTasteGate UniformModulusCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformModulusCompositionFromEventFlow (uniformModulusCompositionToEventFlow x) = some x
    exact UniformModulusCompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformModulusCompositionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformModulusCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformModulusCompositionChapterTasteGate

theorem UniformModulusCompositionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformModulusCompositionDecodeBHist (uniformModulusCompositionEncodeBHist h) = h) ∧
      (forall x : UniformModulusCompositionUp,
        uniformModulusCompositionFromEventFlow (uniformModulusCompositionToEventFlow x) =
          some x) ∧
      (forall x y : UniformModulusCompositionUp,
        uniformModulusCompositionToEventFlow x = uniformModulusCompositionToEventFlow y ->
          x = y) ∧
      uniformModulusCompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UniformModulusCompositionTasteGate_single_carrier_alignment_decode
  constructor
  · exact UniformModulusCompositionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact uniformModulusCompositionToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.UniformModulusCompositionUp
