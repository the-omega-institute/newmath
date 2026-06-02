import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoetherianRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive noetherian_ring_taste_gate_single_carrier_alignment_carrier : Type where
  | mk (C I A G H Q P N : BHist) :
      noetherian_ring_taste_gate_single_carrier_alignment_carrier
  deriving DecidableEq

def noetherianRingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noetherianRingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noetherianRingEncodeBHist h

def noetherianRingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noetherianRingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noetherianRingDecodeBHist tail)

private theorem noetherianRingDecode_encode_bhist :
    ∀ h : BHist, noetherianRingDecodeBHist (noetherianRingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem noetherianRing_mk_congr
    {C C' I I' A A' G G' H H' Q Q' P P' N N' : BHist}
    (hC : C' = C)
    (hI : I' = I)
    (hA : A' = A)
    (hG : G' = G)
    (hH : H' = H)
    (hQ : Q' = Q)
    (hP : P' = P)
    (hN : N' = N) :
    noetherian_ring_taste_gate_single_carrier_alignment_carrier.mk C' I' A' G' H' Q' P' N' =
      noetherian_ring_taste_gate_single_carrier_alignment_carrier.mk C I A G H Q P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hI
  cases hA
  cases hG
  cases hH
  cases hQ
  cases hP
  cases hN
  rfl

def noetherianRingToEventFlow :
    noetherian_ring_taste_gate_single_carrier_alignment_carrier → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | noetherian_ring_taste_gate_single_carrier_alignment_carrier.mk C I A G H Q P N =>
      [noetherianRingEncodeBHist C,
        noetherianRingEncodeBHist I,
        noetherianRingEncodeBHist A,
        noetherianRingEncodeBHist G,
        noetherianRingEncodeBHist H,
        noetherianRingEncodeBHist Q,
        noetherianRingEncodeBHist P,
        noetherianRingEncodeBHist N]

def noetherianRingFromEventFlow :
    EventFlow → Option noetherian_ring_taste_gate_single_carrier_alignment_carrier
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | C :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | A :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (noetherian_ring_taste_gate_single_carrier_alignment_carrier.mk
                                          (noetherianRingDecodeBHist C)
                                          (noetherianRingDecodeBHist I)
                                          (noetherianRingDecodeBHist A)
                                          (noetherianRingDecodeBHist G)
                                          (noetherianRingDecodeBHist H)
                                          (noetherianRingDecodeBHist Q)
                                          (noetherianRingDecodeBHist P)
                                          (noetherianRingDecodeBHist N))
                                  | _ :: _ => none

private theorem noetherianRing_round_trip :
    ∀ x : noetherian_ring_taste_gate_single_carrier_alignment_carrier,
      noetherianRingFromEventFlow (noetherianRingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C I A G H Q P N =>
      exact
        congrArg some
          (noetherianRing_mk_congr
            (noetherianRingDecode_encode_bhist C)
            (noetherianRingDecode_encode_bhist I)
            (noetherianRingDecode_encode_bhist A)
            (noetherianRingDecode_encode_bhist G)
            (noetherianRingDecode_encode_bhist H)
            (noetherianRingDecode_encode_bhist Q)
            (noetherianRingDecode_encode_bhist P)
            (noetherianRingDecode_encode_bhist N))

private theorem noetherianRingToEventFlow_injective
    {x y : noetherian_ring_taste_gate_single_carrier_alignment_carrier} :
    noetherianRingToEventFlow x = noetherianRingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noetherianRingFromEventFlow (noetherianRingToEventFlow x) =
        noetherianRingFromEventFlow (noetherianRingToEventFlow y) :=
    congrArg noetherianRingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (noetherianRing_round_trip x).symm
      (Eq.trans hread (noetherianRing_round_trip y)))

instance noetherianRingBHistCarrier :
    BHistCarrier noetherian_ring_taste_gate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noetherianRingToEventFlow
  fromEventFlow := noetherianRingFromEventFlow

instance noetherianRingChapterTasteGate :
    ChapterTasteGate noetherian_ring_taste_gate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change noetherianRingFromEventFlow (noetherianRingToEventFlow x) = some x
    exact noetherianRing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (noetherianRingToEventFlow_injective heq)

theorem NoetherianRingTasteGate_single_carrier_alignment :
    (∀ h : BHist, noetherianRingDecodeBHist (noetherianRingEncodeBHist h) = h) ∧
      (∀ x : noetherian_ring_taste_gate_single_carrier_alignment_carrier,
        noetherianRingFromEventFlow (noetherianRingToEventFlow x) = some x) ∧
        (∀ x y : noetherian_ring_taste_gate_single_carrier_alignment_carrier,
          noetherianRingToEventFlow x = noetherianRingToEventFlow y → x = y) ∧
          noetherianRingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact noetherianRingDecode_encode_bhist
  · constructor
    · exact noetherianRing_round_trip
    · constructor
      · intro x y heq
        exact noetherianRingToEventFlow_injective heq
      · rfl

end BEDC.Derived.NoetherianRingUp
