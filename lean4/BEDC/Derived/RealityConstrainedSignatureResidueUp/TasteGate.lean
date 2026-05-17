import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSignatureResidueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSignatureResidueUp : Type where
  | mk : (M S G R W H C P N : BHist) -> RealityConstrainedSignatureResidueUp
  deriving DecidableEq

def realityConstrainedSignatureResidueEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSignatureResidueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSignatureResidueEncodeBHist h

def realityConstrainedSignatureResidueDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSignatureResidueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSignatureResidueDecodeBHist tail)

private theorem realityConstrainedSignatureResidueDecode_encode_bhist :
    forall h : BHist,
      realityConstrainedSignatureResidueDecodeBHist
        (realityConstrainedSignatureResidueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem realityConstrainedSignatureResidue_mk_congr
    {M M' S S' G G' R R' W W' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hS : S' = S) (hG : G' = G) (hR : R' = R)
    (hW : W' = W) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    RealityConstrainedSignatureResidueUp.mk M' S' G' R' W' H' C' P' N' =
      RealityConstrainedSignatureResidueUp.mk M S G R W H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hS
  cases hG
  cases hR
  cases hW
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realityConstrainedSignatureResidueToEventFlow :
    RealityConstrainedSignatureResidueUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureResidueUp.mk M S G R W H C P N =>
      [[BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist M,
        [BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist N]

def realityConstrainedSignatureResidueFromEventFlow :
    EventFlow -> Option RealityConstrainedSignatureResidueUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: M :: _tag1 :: S :: _tag2 :: G :: _tag3 :: R :: _tag4 :: W ::
      _tag5 :: H :: _tag6 :: C :: _tag7 :: P :: _tag8 :: N :: [] =>
      some
        (RealityConstrainedSignatureResidueUp.mk
          (realityConstrainedSignatureResidueDecodeBHist M)
          (realityConstrainedSignatureResidueDecodeBHist S)
          (realityConstrainedSignatureResidueDecodeBHist G)
          (realityConstrainedSignatureResidueDecodeBHist R)
          (realityConstrainedSignatureResidueDecodeBHist W)
          (realityConstrainedSignatureResidueDecodeBHist H)
          (realityConstrainedSignatureResidueDecodeBHist C)
          (realityConstrainedSignatureResidueDecodeBHist P)
          (realityConstrainedSignatureResidueDecodeBHist N))
  | _ => none

private theorem realityConstrainedSignatureResidue_round_trip :
    forall x : RealityConstrainedSignatureResidueUp,
      realityConstrainedSignatureResidueFromEventFlow
        (realityConstrainedSignatureResidueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S G R W H C P N =>
      change
        some
          (RealityConstrainedSignatureResidueUp.mk
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist M))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist S))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist G))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist R))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist W))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist H))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist C))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist P))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist N))) =
          some (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N)
      exact
        congrArg some
          (realityConstrainedSignatureResidue_mk_congr
            (realityConstrainedSignatureResidueDecode_encode_bhist M)
            (realityConstrainedSignatureResidueDecode_encode_bhist S)
            (realityConstrainedSignatureResidueDecode_encode_bhist G)
            (realityConstrainedSignatureResidueDecode_encode_bhist R)
            (realityConstrainedSignatureResidueDecode_encode_bhist W)
            (realityConstrainedSignatureResidueDecode_encode_bhist H)
            (realityConstrainedSignatureResidueDecode_encode_bhist C)
            (realityConstrainedSignatureResidueDecode_encode_bhist P)
            (realityConstrainedSignatureResidueDecode_encode_bhist N))

private theorem realityConstrainedSignatureResidueToEventFlow_injective
    {x y : RealityConstrainedSignatureResidueUp} :
    realityConstrainedSignatureResidueToEventFlow x =
      realityConstrainedSignatureResidueToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSignatureResidueFromEventFlow
          (realityConstrainedSignatureResidueToEventFlow x) =
        realityConstrainedSignatureResidueFromEventFlow
          (realityConstrainedSignatureResidueToEventFlow y) :=
    congrArg realityConstrainedSignatureResidueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedSignatureResidue_round_trip x).symm
      (Eq.trans hread (realityConstrainedSignatureResidue_round_trip y)))

def realityConstrainedSignatureResidueFields :
    RealityConstrainedSignatureResidueUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureResidueUp.mk M S G R W H C P N =>
      [M, S, G, R, W, H, C, P, N]

private theorem realityConstrainedSignatureResidue_field_faithful :
    forall x y : RealityConstrainedSignatureResidueUp,
      realityConstrainedSignatureResidueFields x =
        realityConstrainedSignatureResidueFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 S1 G1 R1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 S2 G2 R2 W2 H2 C2 P2 N2 =>
          injection hfields with hM hRest1
          injection hRest1 with hS hRest2
          injection hRest2 with hG hRest3
          injection hRest3 with hR hRest4
          injection hRest4 with hW hRest5
          injection hRest5 with hH hRest6
          injection hRest6 with hC hRest7
          injection hRest7 with hP hRest8
          injection hRest8 with hN _
          cases hM
          cases hS
          cases hG
          cases hR
          cases hW
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance realityConstrainedSignatureResidueBHistCarrier :
    BHistCarrier RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSignatureResidueToEventFlow
  fromEventFlow := realityConstrainedSignatureResidueFromEventFlow

instance realityConstrainedSignatureResidueChapterTasteGate :
    ChapterTasteGate RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSignatureResidueFromEventFlow
        (realityConstrainedSignatureResidueToEventFlow x) = some x
    exact realityConstrainedSignatureResidue_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSignatureResidueToEventFlow_injective heq)

instance realityConstrainedSignatureResidueFieldFaithful :
    FieldFaithful RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSignatureResidueFields
  field_faithful := realityConstrainedSignatureResidue_field_faithful

instance realityConstrainedSignatureResidueNontrivial :
    Nontrivial RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSignatureResidueUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedSignatureResidueUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSignatureResidueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSignatureResidueChapterTasteGate

theorem RealityConstrainedSignatureResidueTasteGate_single_carrier_alignment :
    (forall h : BHist,
      realityConstrainedSignatureResidueDecodeBHist
        (realityConstrainedSignatureResidueEncodeBHist h) = h) ∧
      (forall M S G R W H C P N : BHist,
        realityConstrainedSignatureResidueToEventFlow
            (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N) =
          [[BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist M,
            [BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist S,
            [BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist G,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist R,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist W,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist H,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist C,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist P,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist N]) ∧
        (forall M S G R W H C P N : BHist,
          realityConstrainedSignatureResidueFields
              (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N) =
            [M, S, G, R, W, H, C, P, N]) ∧
          realityConstrainedSignatureResidueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realityConstrainedSignatureResidueDecode_encode_bhist
  · constructor
    · intro M S G R W H C P N
      rfl
    · constructor
      · intro M S G R W H C P N
        rfl
      · rfl

namespace TasteGate

theorem RealityConstrainedSignatureResidueTasteGate_single_carrier_alignment :
    (forall h : BHist,
      realityConstrainedSignatureResidueDecodeBHist
        (realityConstrainedSignatureResidueEncodeBHist h) = h) ∧
      (forall M S G R W H C P N : BHist,
        realityConstrainedSignatureResidueToEventFlow
            (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N) =
          [[BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist M,
            [BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist S,
            [BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist G,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist R,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist W,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist H,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist C,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist P,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist N]) ∧
        (forall M S G R W H C P N : BHist,
          realityConstrainedSignatureResidueFields
              (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N) =
            [M, S, G, R, W, H, C, P, N]) ∧
          realityConstrainedSignatureResidueEncodeBHist BHist.Empty = ([] : List BMark) :=
  RealityConstrainedSignatureResidueUp.RealityConstrainedSignatureResidueTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.RealityConstrainedSignatureResidueUp
