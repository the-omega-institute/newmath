import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialArchimedeanRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialArchimedeanRealUp : Type where
  | mk (R i Q D W G E H C P N : BHist) : SequentialArchimedeanRealUp
  deriving DecidableEq

def sequentialArchimedeanRealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialArchimedeanRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialArchimedeanRealEncodeBHist h

def sequentialArchimedeanRealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialArchimedeanRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialArchimedeanRealDecodeBHist tail)

private theorem SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      sequentialArchimedeanRealDecodeBHist (sequentialArchimedeanRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialArchimedeanRealFields : SequentialArchimedeanRealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialArchimedeanRealUp.mk R i Q D W G E H C P N =>
      [R, i, Q, D, W, G, E, H, C, P, N]

def sequentialArchimedeanRealToEventFlow : SequentialArchimedeanRealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialArchimedeanRealFields x).map sequentialArchimedeanRealEncodeBHist

def sequentialArchimedeanRealFromEventFlow : EventFlow -> Option SequentialArchimedeanRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: restR =>
      match restR with
      | i :: restI =>
          match restI with
          | Q :: restQ =>
              match restQ with
              | D :: restD =>
                  match restD with
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
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (SequentialArchimedeanRealUp.mk
                                                      (sequentialArchimedeanRealDecodeBHist R)
                                                      (sequentialArchimedeanRealDecodeBHist i)
                                                      (sequentialArchimedeanRealDecodeBHist Q)
                                                      (sequentialArchimedeanRealDecodeBHist D)
                                                      (sequentialArchimedeanRealDecodeBHist W)
                                                      (sequentialArchimedeanRealDecodeBHist G)
                                                      (sequentialArchimedeanRealDecodeBHist E)
                                                      (sequentialArchimedeanRealDecodeBHist H)
                                                      (sequentialArchimedeanRealDecodeBHist C)
                                                      (sequentialArchimedeanRealDecodeBHist P)
                                                      (sequentialArchimedeanRealDecodeBHist N))
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

private theorem SequentialArchimedeanRealTasteGate_single_carrier_alignment_mk_congr
    {R R' i i' Q Q' D D' W W' G G' E E' H H' C C' P P' N N' : BHist}
    (hR : R' = R) (hi : i' = i) (hQ : Q' = Q) (hD : D' = D)
    (hW : W' = W) (hG : G' = G) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    SequentialArchimedeanRealUp.mk R' i' Q' D' W' G' E' H' C' P' N' =
      SequentialArchimedeanRealUp.mk R i Q D W G E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hi
  cases hQ
  cases hD
  cases hW
  cases hG
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem SequentialArchimedeanRealTasteGate_single_carrier_alignment_round_trip :
    forall x : SequentialArchimedeanRealUp,
      sequentialArchimedeanRealFromEventFlow (sequentialArchimedeanRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R i Q D W G E H C P N =>
      exact
        congrArg some
          (SequentialArchimedeanRealTasteGate_single_carrier_alignment_mk_congr
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode R)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode i)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode Q)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode D)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode W)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode G)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode E)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode H)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode C)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode P)
            (SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode N))

private theorem
    SequentialArchimedeanRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialArchimedeanRealUp} :
    sequentialArchimedeanRealToEventFlow x = sequentialArchimedeanRealToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialArchimedeanRealFromEventFlow (sequentialArchimedeanRealToEventFlow x) =
        sequentialArchimedeanRealFromEventFlow (sequentialArchimedeanRealToEventFlow y) :=
    congrArg sequentialArchimedeanRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentialArchimedeanRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentialArchimedeanRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem SequentialArchimedeanRealTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : SequentialArchimedeanRealUp,
      sequentialArchimedeanRealFields x = sequentialArchimedeanRealFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R i Q D W G E H C P N =>
      cases y with
      | mk R' i' Q' D' W' G' E' H' C' P' N' =>
          cases hfields
          rfl

instance sequentialArchimedeanRealBHistCarrier :
    BHistCarrier SequentialArchimedeanRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialArchimedeanRealToEventFlow
  fromEventFlow := sequentialArchimedeanRealFromEventFlow

instance sequentialArchimedeanRealChapterTasteGate :
    ChapterTasteGate SequentialArchimedeanRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentialArchimedeanRealFromEventFlow (sequentialArchimedeanRealToEventFlow x) =
        some x
    exact SequentialArchimedeanRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentialArchimedeanRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sequentialArchimedeanRealFieldFaithful :
    FieldFaithful SequentialArchimedeanRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentialArchimedeanRealFields
  field_faithful := SequentialArchimedeanRealTasteGate_single_carrier_alignment_fields_faithful

instance sequentialArchimedeanRealNontrivial :
    Nontrivial SequentialArchimedeanRealUp where
  witness_pair :=
    ⟨SequentialArchimedeanRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SequentialArchimedeanRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SequentialArchimedeanRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentialArchimedeanRealChapterTasteGate

theorem SequentialArchimedeanRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SequentialArchimedeanRealUp) ∧
      Nonempty (FieldFaithful SequentialArchimedeanRealUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SequentialArchimedeanRealUp) ∧
          (forall h : BHist,
            sequentialArchimedeanRealDecodeBHist
              (sequentialArchimedeanRealEncodeBHist h) = h) ∧
            (forall x : SequentialArchimedeanRealUp,
              sequentialArchimedeanRealFromEventFlow
                  (sequentialArchimedeanRealToEventFlow x) =
                some x) ∧
              sequentialArchimedeanRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨sequentialArchimedeanRealChapterTasteGate⟩,
      ⟨sequentialArchimedeanRealFieldFaithful⟩,
      ⟨sequentialArchimedeanRealNontrivial⟩,
      SequentialArchimedeanRealTasteGate_single_carrier_alignment_decode_encode,
      SequentialArchimedeanRealTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.SequentialArchimedeanRealUp
