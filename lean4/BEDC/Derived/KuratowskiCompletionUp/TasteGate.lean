import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiCompletionUp : Type where
  | mk (M E D S A U R H C P N : BHist) : KuratowskiCompletionUp
  deriving DecidableEq

def kuratowskiCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiCompletionEncodeBHist h

def kuratowskiCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiCompletionDecodeBHist tail)

private theorem KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      kuratowskiCompletionDecodeBHist (kuratowskiCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiCompletionFields : KuratowskiCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiCompletionUp.mk M E D S A U R H C P N => [M, E, D, S, A, U, R, H, C, P, N]

def kuratowskiCompletionToEventFlow : KuratowskiCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kuratowskiCompletionFields x).map kuratowskiCompletionEncodeBHist

def kuratowskiCompletionFromEventFlow : EventFlow → Option KuratowskiCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | E :: restE =>
          match restE with
          | D :: restD =>
              match restD with
              | S :: restS =>
                  match restS with
                  | A :: restA =>
                      match restA with
                      | U :: restU =>
                          match restU with
                          | R :: restR =>
                              match restR with
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
                                                    (KuratowskiCompletionUp.mk
                                                      (kuratowskiCompletionDecodeBHist M)
                                                      (kuratowskiCompletionDecodeBHist E)
                                                      (kuratowskiCompletionDecodeBHist D)
                                                      (kuratowskiCompletionDecodeBHist S)
                                                      (kuratowskiCompletionDecodeBHist A)
                                                      (kuratowskiCompletionDecodeBHist U)
                                                      (kuratowskiCompletionDecodeBHist R)
                                                      (kuratowskiCompletionDecodeBHist H)
                                                      (kuratowskiCompletionDecodeBHist C)
                                                      (kuratowskiCompletionDecodeBHist P)
                                                      (kuratowskiCompletionDecodeBHist N))
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

private theorem KuratowskiCompletionTasteGate_single_carrier_alignment_mk_congr
    {M M' E E' D D' S S' A A' U U' R R' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hE : E' = E) (hD : D' = D) (hS : S' = S)
    (hA : A' = A) (hU : U' = U) (hR : R' = R) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    KuratowskiCompletionUp.mk M' E' D' S' A' U' R' H' C' P' N' =
      KuratowskiCompletionUp.mk M E D S A U R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hE
  cases hD
  cases hS
  cases hA
  cases hU
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem KuratowskiCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KuratowskiCompletionUp,
      kuratowskiCompletionFromEventFlow (kuratowskiCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E D S A U R H C P N =>
      exact
        congrArg some
          (KuratowskiCompletionTasteGate_single_carrier_alignment_mk_congr
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode M)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode E)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode D)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode S)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode A)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode U)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode R)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode H)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode C)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode P)
            (KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode N))

private theorem KuratowskiCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KuratowskiCompletionUp} :
    kuratowskiCompletionToEventFlow x = kuratowskiCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiCompletionFromEventFlow (kuratowskiCompletionToEventFlow x) =
        kuratowskiCompletionFromEventFlow (kuratowskiCompletionToEventFlow y) :=
    congrArg kuratowskiCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KuratowskiCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KuratowskiCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance kuratowskiCompletionBHistCarrier : BHistCarrier KuratowskiCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiCompletionToEventFlow
  fromEventFlow := kuratowskiCompletionFromEventFlow

instance kuratowskiCompletionChapterTasteGate : ChapterTasteGate KuratowskiCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiCompletionFromEventFlow (kuratowskiCompletionToEventFlow x) = some x
    exact KuratowskiCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KuratowskiCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate KuratowskiCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kuratowskiCompletionChapterTasteGate

theorem KuratowskiCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        kuratowskiCompletionDecodeBHist (kuratowskiCompletionEncodeBHist h) = h) ∧
      (∀ x : KuratowskiCompletionUp,
        kuratowskiCompletionFromEventFlow (kuratowskiCompletionToEventFlow x) = some x) ∧
      (∀ x y : KuratowskiCompletionUp,
        kuratowskiCompletionToEventFlow x = kuratowskiCompletionToEventFlow y → x = y) ∧
      kuratowskiCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact KuratowskiCompletionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact KuratowskiCompletionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact KuratowskiCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.KuratowskiCompletionUp
