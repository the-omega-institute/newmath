import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntermediateValueBisectionUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntermediateValueBisectionUp : Type where
  | mk (J R D S W G E H C P N : BHist) : IntermediateValueBisectionUp
  deriving DecidableEq

def intermediateValueBisectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intermediateValueBisectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intermediateValueBisectionEncodeBHist h

def intermediateValueBisectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intermediateValueBisectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intermediateValueBisectionDecodeBHist tail)

private theorem IntermediateValueBisectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      intermediateValueBisectionDecodeBHist (intermediateValueBisectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intermediateValueBisectionFields : IntermediateValueBisectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueBisectionUp.mk J R D S W G E H C P N =>
      [J, R, D, S, W, G, E, H, C, P, N]

def intermediateValueBisectionToEventFlow : IntermediateValueBisectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (intermediateValueBisectionFields x).map intermediateValueBisectionEncodeBHist

def intermediateValueBisectionFromEventFlow : EventFlow → Option IntermediateValueBisectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | J :: restJ =>
      match restJ with
      | R :: restR =>
          match restR with
          | D :: restD =>
              match restD with
              | S :: restS =>
                  match restS with
                  | W :: restW =>
                      match restW with
                      | G :: restG =>
                          match restG with
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
                                                    (IntermediateValueBisectionUp.mk
                                                      (intermediateValueBisectionDecodeBHist J)
                                                      (intermediateValueBisectionDecodeBHist R)
                                                      (intermediateValueBisectionDecodeBHist D)
                                                      (intermediateValueBisectionDecodeBHist S)
                                                      (intermediateValueBisectionDecodeBHist W)
                                                      (intermediateValueBisectionDecodeBHist G)
                                                      (intermediateValueBisectionDecodeBHist E)
                                                      (intermediateValueBisectionDecodeBHist H)
                                                      (intermediateValueBisectionDecodeBHist C)
                                                      (intermediateValueBisectionDecodeBHist P)
                                                      (intermediateValueBisectionDecodeBHist N))
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

private theorem intermediateValueBisection_mk_congr
    {J J' R R' D D' S S' W W' G G' E E' H H' C C' P P' N N' : BHist}
    (hJ : J' = J) (hR : R' = R) (hD : D' = D) (hS : S' = S)
    (hW : W' = W) (hG : G' = G) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    IntermediateValueBisectionUp.mk J' R' D' S' W' G' E' H' C' P' N' =
      IntermediateValueBisectionUp.mk J R D S W G E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hJ
  cases hR
  cases hD
  cases hS
  cases hW
  cases hG
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntermediateValueBisectionUp,
      intermediateValueBisectionFromEventFlow (intermediateValueBisectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J R D S W G E H C P N =>
      exact
        congrArg some
          (intermediateValueBisection_mk_congr
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode J)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode R)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode D)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode S)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode W)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode G)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode E)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode H)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode C)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode P)
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decode N))

private theorem IntermediateValueBisectionTasteGate_single_carrier_alignment_injective
    {x y : IntermediateValueBisectionUp} :
    intermediateValueBisectionToEventFlow x = intermediateValueBisectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intermediateValueBisectionFromEventFlow (intermediateValueBisectionToEventFlow x) =
        intermediateValueBisectionFromEventFlow (intermediateValueBisectionToEventFlow y) :=
    congrArg intermediateValueBisectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem intermediateValueBisection_field_faithful :
    ∀ x y : IntermediateValueBisectionUp,
      intermediateValueBisectionFields x = intermediateValueBisectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk J R D S W G E H C P N =>
      cases y with
      | mk J' R' D' S' W' G' E' H' C' P' N' =>
          cases hfields
          rfl

instance intermediateValueBisectionBHistCarrier :
    BHistCarrier IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intermediateValueBisectionToEventFlow
  fromEventFlow := intermediateValueBisectionFromEventFlow

instance intermediateValueBisectionChapterTasteGate :
    ChapterTasteGate IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intermediateValueBisectionFromEventFlow (intermediateValueBisectionToEventFlow x) =
        some x
    exact IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntermediateValueBisectionTasteGate_single_carrier_alignment_injective heq)

instance intermediateValueBisectionFieldFaithful :
    FieldFaithful IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := intermediateValueBisectionFields
  field_faithful := intermediateValueBisection_field_faithful

instance intermediateValueBisectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntermediateValueBisectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IntermediateValueBisectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate IntermediateValueBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intermediateValueBisectionChapterTasteGate

theorem IntermediateValueBisectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate IntermediateValueBisectionUp) ∧
      Nonempty (FieldFaithful IntermediateValueBisectionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial IntermediateValueBisectionUp) ∧
      (∀ h : BHist,
        intermediateValueBisectionDecodeBHist (intermediateValueBisectionEncodeBHist h) =
          h) ∧
      (∀ x : IntermediateValueBisectionUp,
        intermediateValueBisectionFromEventFlow (intermediateValueBisectionToEventFlow x) =
          some x) ∧
      (∀ x y : IntermediateValueBisectionUp,
        intermediateValueBisectionToEventFlow x = intermediateValueBisectionToEventFlow y →
          x = y) ∧
      intermediateValueBisectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨intermediateValueBisectionChapterTasteGate⟩
  constructor
  · exact ⟨intermediateValueBisectionFieldFaithful⟩
  constructor
  · exact ⟨intermediateValueBisectionNontrivial⟩
  constructor
  · exact IntermediateValueBisectionTasteGate_single_carrier_alignment_decode
  constructor
  · exact IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact IntermediateValueBisectionTasteGate_single_carrier_alignment_injective heq
  · rfl

end TasteGate
end BEDC.Derived.IntermediateValueBisectionUp
