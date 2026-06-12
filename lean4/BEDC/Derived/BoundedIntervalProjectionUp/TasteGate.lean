import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedIntervalProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedIntervalProjectionUp : Type where
  | mk (X L U D W R I C H T P N : BHist) : BoundedIntervalProjectionUp
  deriving DecidableEq

def boundedIntervalProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedIntervalProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedIntervalProjectionEncodeBHist h

def boundedIntervalProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedIntervalProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedIntervalProjectionDecodeBHist tail)

private theorem BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedIntervalProjectionDecodeBHist (boundedIntervalProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedIntervalProjectionFields : BoundedIntervalProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedIntervalProjectionUp.mk X L U D W R I C H T P N =>
      [X, L, U, D, W, R, I, C, H, T, P, N]

def boundedIntervalProjectionToEventFlow : BoundedIntervalProjectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedIntervalProjectionFields x).map boundedIntervalProjectionEncodeBHist

def boundedIntervalProjectionFromEventFlow : EventFlow → Option BoundedIntervalProjectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | L :: restL =>
          match restL with
          | U :: restU =>
              match restU with
              | D :: restD =>
                  match restD with
                  | W :: restW =>
                      match restW with
                      | R :: restR =>
                          match restR with
                          | I :: restI =>
                              match restI with
                              | C :: restC =>
                                  match restC with
                                  | H :: restH =>
                                      match restH with
                                      | T :: restT =>
                                          match restT with
                                          | P :: restP =>
                                              match restP with
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (BoundedIntervalProjectionUp.mk
                                                          (boundedIntervalProjectionDecodeBHist X)
                                                          (boundedIntervalProjectionDecodeBHist L)
                                                          (boundedIntervalProjectionDecodeBHist U)
                                                          (boundedIntervalProjectionDecodeBHist D)
                                                          (boundedIntervalProjectionDecodeBHist W)
                                                          (boundedIntervalProjectionDecodeBHist R)
                                                          (boundedIntervalProjectionDecodeBHist I)
                                                          (boundedIntervalProjectionDecodeBHist C)
                                                          (boundedIntervalProjectionDecodeBHist H)
                                                          (boundedIntervalProjectionDecodeBHist T)
                                                          (boundedIntervalProjectionDecodeBHist P)
                                                          (boundedIntervalProjectionDecodeBHist N))
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

private theorem boundedIntervalProjection_mk_congr
    {X X' L L' U U' D D' W W' R R' I I' C C' H H' T T' P P' N N' : BHist}
    (hX : X' = X) (hL : L' = L) (hU : U' = U) (hD : D' = D)
    (hW : W' = W) (hR : R' = R) (hI : I' = I) (hC : C' = C)
    (hH : H' = H) (hT : T' = T) (hP : P' = P) (hN : N' = N) :
    BoundedIntervalProjectionUp.mk X' L' U' D' W' R' I' C' H' T' P' N' =
      BoundedIntervalProjectionUp.mk X L U D W R I C H T P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hL
  cases hU
  cases hD
  cases hW
  cases hR
  cases hI
  cases hC
  cases hH
  cases hT
  cases hP
  cases hN
  rfl

private theorem BoundedIntervalProjectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedIntervalProjectionUp,
      boundedIntervalProjectionFromEventFlow (boundedIntervalProjectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X L U D W R I C H T P N =>
      exact
        congrArg some
          (boundedIntervalProjection_mk_congr
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode X)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode L)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode U)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode D)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode W)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode R)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode I)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode C)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode H)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode T)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode P)
            (BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode N))

private theorem boundedIntervalProjectionToEventFlow_injective {x y : BoundedIntervalProjectionUp} :
    boundedIntervalProjectionToEventFlow x = boundedIntervalProjectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedIntervalProjectionFromEventFlow (boundedIntervalProjectionToEventFlow x) =
        boundedIntervalProjectionFromEventFlow (boundedIntervalProjectionToEventFlow y) :=
    congrArg boundedIntervalProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedIntervalProjectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedIntervalProjectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem boundedIntervalProjection_field_faithful :
    ∀ x y : BoundedIntervalProjectionUp,
      boundedIntervalProjectionFields x = boundedIntervalProjectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X L U D W R I C H T P N =>
      cases y with
      | mk X' L' U' D' W' R' I' C' H' T' P' N' =>
          cases hfields
          rfl

instance boundedIntervalProjectionBHistCarrier : BHistCarrier BoundedIntervalProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedIntervalProjectionToEventFlow
  fromEventFlow := boundedIntervalProjectionFromEventFlow

instance boundedIntervalProjectionChapterTasteGate :
    ChapterTasteGate BoundedIntervalProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedIntervalProjectionFromEventFlow (boundedIntervalProjectionToEventFlow x) = some x
    exact BoundedIntervalProjectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedIntervalProjectionToEventFlow_injective heq)

instance boundedIntervalProjectionFieldFaithful : FieldFaithful BoundedIntervalProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedIntervalProjectionFields
  field_faithful := boundedIntervalProjection_field_faithful

instance boundedIntervalProjectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BoundedIntervalProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedIntervalProjectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BoundedIntervalProjectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedIntervalProjectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedIntervalProjectionUp) ∧
      Nonempty (FieldFaithful BoundedIntervalProjectionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedIntervalProjectionUp) ∧
      (∀ h : BHist,
        boundedIntervalProjectionDecodeBHist (boundedIntervalProjectionEncodeBHist h) = h) ∧
      (∀ x : BoundedIntervalProjectionUp,
        boundedIntervalProjectionFromEventFlow (boundedIntervalProjectionToEventFlow x) = some x) ∧
      boundedIntervalProjectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨boundedIntervalProjectionChapterTasteGate⟩,
      ⟨boundedIntervalProjectionFieldFaithful⟩,
      ⟨boundedIntervalProjectionNontrivial⟩,
      BoundedIntervalProjectionTasteGate_single_carrier_alignment_decode,
      BoundedIntervalProjectionTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.BoundedIntervalProjectionUp
