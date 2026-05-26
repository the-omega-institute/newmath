import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailBoundUp : Type where
  | mk (M S D R E B H C P N : BHist) : CauchyTailBoundUp
  deriving DecidableEq

def cauchyTailBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailBoundEncodeBHist h

def cauchyTailBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailBoundDecodeBHist tail)

private theorem CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyTailBoundDecodeBHist (cauchyTailBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailBoundFields : CauchyTailBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailBoundUp.mk M S D R E B H C P N => [M, S, D, R, E, B, H, C, P, N]

def cauchyTailBoundToEventFlow : CauchyTailBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailBoundFields x).map cauchyTailBoundEncodeBHist

def cauchyTailBoundFromEventFlow : EventFlow → Option CauchyTailBoundUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | S :: restS =>
          match restS with
          | D :: restD =>
              match restD with
              | R :: restR =>
                  match restR with
                  | E :: restE =>
                      match restE with
                      | B :: restB =>
                          match restB with
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
                                                (CauchyTailBoundUp.mk
                                                  (cauchyTailBoundDecodeBHist M)
                                                  (cauchyTailBoundDecodeBHist S)
                                                  (cauchyTailBoundDecodeBHist D)
                                                  (cauchyTailBoundDecodeBHist R)
                                                  (cauchyTailBoundDecodeBHist E)
                                                  (cauchyTailBoundDecodeBHist B)
                                                  (cauchyTailBoundDecodeBHist H)
                                                  (cauchyTailBoundDecodeBHist C)
                                                  (cauchyTailBoundDecodeBHist P)
                                                  (cauchyTailBoundDecodeBHist N))
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

private theorem CauchyTailBoundTasteGate_single_carrier_alignment_mk_congr
    {M M' S S' D D' R R' E E' B B' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hS : S' = S) (hD : D' = D) (hR : R' = R)
    (hE : E' = E) (hB : B' = B) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyTailBoundUp.mk M' S' D' R' E' B' H' C' P' N' =
      CauchyTailBoundUp.mk M S D R E B H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hS
  cases hD
  cases hR
  cases hE
  cases hB
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyTailBoundTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyTailBoundUp,
      cauchyTailBoundFromEventFlow (cauchyTailBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D R E B H C P N =>
      exact
        congrArg some
          (CauchyTailBoundTasteGate_single_carrier_alignment_mk_congr
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode M)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode S)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode D)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode R)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode E)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode B)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode H)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode C)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode P)
            (CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode N))

private theorem CauchyTailBoundTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailBoundUp} :
    cauchyTailBoundToEventFlow x = cauchyTailBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailBoundFromEventFlow (cauchyTailBoundToEventFlow x) =
        cauchyTailBoundFromEventFlow (cauchyTailBoundToEventFlow y) :=
    congrArg cauchyTailBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailBoundTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailBoundTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyTailBoundBHistCarrier : BHistCarrier CauchyTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailBoundToEventFlow
  fromEventFlow := cauchyTailBoundFromEventFlow

instance cauchyTailBoundChapterTasteGate : ChapterTasteGate CauchyTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailBoundFromEventFlow (cauchyTailBoundToEventFlow x) = some x
    exact CauchyTailBoundTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailBoundTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyTailBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailBoundChapterTasteGate

theorem CauchyTailBoundTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailBoundDecodeBHist (cauchyTailBoundEncodeBHist h) = h) ∧
      (∀ x : CauchyTailBoundUp,
        cauchyTailBoundFromEventFlow (cauchyTailBoundToEventFlow x) = some x) ∧
      (∀ x y : CauchyTailBoundUp,
        cauchyTailBoundToEventFlow x = cauchyTailBoundToEventFlow y → x = y) ∧
      cauchyTailBoundEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyTailBoundTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact CauchyTailBoundTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact CauchyTailBoundTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyTailBoundUp
