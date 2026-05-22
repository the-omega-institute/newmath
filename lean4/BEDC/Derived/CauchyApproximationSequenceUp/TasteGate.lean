import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyApproximationSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyApproximationSequenceUp : Type where
  | mk (Q D S R E H C P N : BHist) : CauchyApproximationSequenceUp
  deriving DecidableEq

def cauchyApproximationSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyApproximationSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyApproximationSequenceEncodeBHist h

def cauchyApproximationSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyApproximationSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyApproximationSequenceDecodeBHist tail)

theorem CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyApproximationSequenceDecodeBHist
        (cauchyApproximationSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyApproximationSequenceFields : CauchyApproximationSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyApproximationSequenceUp.mk Q D S R E H C P N => [Q, D, S, R, E, H, C, P, N]

def cauchyApproximationSequenceToEventFlow : CauchyApproximationSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyApproximationSequenceFields x).map cauchyApproximationSequenceEncodeBHist

def cauchyApproximationSequenceFromEventFlow :
    EventFlow → Option CauchyApproximationSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _Q :: [] => none
  | _Q :: _D :: [] => none
  | _Q :: _D :: _S :: [] => none
  | _Q :: _D :: _S :: _R :: [] => none
  | _Q :: _D :: _S :: _R :: _E :: [] => none
  | _Q :: _D :: _S :: _R :: _E :: _H :: [] => none
  | _Q :: _D :: _S :: _R :: _E :: _H :: _C :: [] => none
  | _Q :: _D :: _S :: _R :: _E :: _H :: _C :: _P :: [] => none
  | Q :: D :: S :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (CauchyApproximationSequenceUp.mk
          (cauchyApproximationSequenceDecodeBHist Q)
          (cauchyApproximationSequenceDecodeBHist D)
          (cauchyApproximationSequenceDecodeBHist S)
          (cauchyApproximationSequenceDecodeBHist R)
          (cauchyApproximationSequenceDecodeBHist E)
          (cauchyApproximationSequenceDecodeBHist H)
          (cauchyApproximationSequenceDecodeBHist C)
          (cauchyApproximationSequenceDecodeBHist P)
          (cauchyApproximationSequenceDecodeBHist N))
  | _Q :: _D :: _S :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem cauchyApproximationSequence_mk_congr
    {Q Q' D D' S S' R R' E E' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q) (hD : D' = D) (hS : S' = S) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    CauchyApproximationSequenceUp.mk Q' D' S' R' E' H' C' P' N' =
      CauchyApproximationSequenceUp.mk Q D S R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hD
  cases hS
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

theorem CauchyApproximationSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyApproximationSequenceUp,
      cauchyApproximationSequenceFromEventFlow
          (cauchyApproximationSequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D S R E H C P N =>
      exact
        congrArg some
          (cauchyApproximationSequence_mk_congr
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode Q)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode D)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode S)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode R)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode E)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode H)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode C)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode P)
            (CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode N))

theorem CauchyApproximationSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyApproximationSequenceUp} :
    cauchyApproximationSequenceToEventFlow x =
      cauchyApproximationSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyApproximationSequenceFromEventFlow (cauchyApproximationSequenceToEventFlow x) =
        cauchyApproximationSequenceFromEventFlow (cauchyApproximationSequenceToEventFlow y) :=
    congrArg cauchyApproximationSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyApproximationSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyApproximationSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyApproximationSequenceBHistCarrier :
    BHistCarrier CauchyApproximationSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyApproximationSequenceToEventFlow
  fromEventFlow := cauchyApproximationSequenceFromEventFlow

instance cauchyApproximationSequenceChapterTasteGate :
    ChapterTasteGate CauchyApproximationSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyApproximationSequenceFromEventFlow
          (cauchyApproximationSequenceToEventFlow x) =
        some x
    exact CauchyApproximationSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyApproximationSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyApproximationSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyApproximationSequenceChapterTasteGate

theorem CauchyApproximationSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyApproximationSequenceDecodeBHist
        (cauchyApproximationSequenceEncodeBHist h) = h) ∧
      (∀ x : CauchyApproximationSequenceUp,
        cauchyApproximationSequenceFromEventFlow
            (cauchyApproximationSequenceToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyApproximationSequenceUp,
        cauchyApproximationSequenceToEventFlow x =
          cauchyApproximationSequenceToEventFlow y → x = y) ∧
      cauchyApproximationSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyApproximationSequenceTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact CauchyApproximationSequenceTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact CauchyApproximationSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyApproximationSequenceUp
