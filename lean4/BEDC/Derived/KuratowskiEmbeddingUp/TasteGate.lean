import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiEmbeddingUp : Type where
  | mk (M B D T I H C P N : BHist) : KuratowskiEmbeddingUp
  deriving DecidableEq

def kuratowskiEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiEmbeddingEncodeBHist h

def kuratowskiEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiEmbeddingDecodeBHist tail)

private theorem kuratowskiEmbedding_decode_encode_bhist :
    ∀ h : BHist, kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem kuratowskiEmbedding_mk_congr
    {M M' B B' D D' T T' I I' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hB : B' = B) (hD : D' = D) (hT : T' = T)
    (hI : I' = I) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    KuratowskiEmbeddingUp.mk M' B' D' T' I' H' C' P' N' =
      KuratowskiEmbeddingUp.mk M B D T I H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hB
  cases hD
  cases hT
  cases hI
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def kuratowskiEmbeddingFields : KuratowskiEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiEmbeddingUp.mk M B D T I H C P N => [M, B, D, T, I, H, C, P, N]

def kuratowskiEmbeddingToEventFlow : KuratowskiEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kuratowskiEmbeddingFields x).map kuratowskiEmbeddingEncodeBHist

def kuratowskiEmbeddingFromEventFlow : EventFlow → Option KuratowskiEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | I :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (KuratowskiEmbeddingUp.mk
                                              (kuratowskiEmbeddingDecodeBHist M)
                                              (kuratowskiEmbeddingDecodeBHist B)
                                              (kuratowskiEmbeddingDecodeBHist D)
                                              (kuratowskiEmbeddingDecodeBHist T)
                                              (kuratowskiEmbeddingDecodeBHist I)
                                              (kuratowskiEmbeddingDecodeBHist H)
                                              (kuratowskiEmbeddingDecodeBHist C)
                                              (kuratowskiEmbeddingDecodeBHist P)
                                              (kuratowskiEmbeddingDecodeBHist N))
                                      | _ :: _ => none

private theorem kuratowskiEmbedding_round_trip :
    ∀ x : KuratowskiEmbeddingUp,
      kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B D T I H C P N =>
      exact
        congrArg some
          (kuratowskiEmbedding_mk_congr
            (kuratowskiEmbedding_decode_encode_bhist M)
            (kuratowskiEmbedding_decode_encode_bhist B)
            (kuratowskiEmbedding_decode_encode_bhist D)
            (kuratowskiEmbedding_decode_encode_bhist T)
            (kuratowskiEmbedding_decode_encode_bhist I)
            (kuratowskiEmbedding_decode_encode_bhist H)
            (kuratowskiEmbedding_decode_encode_bhist C)
            (kuratowskiEmbedding_decode_encode_bhist P)
            (kuratowskiEmbedding_decode_encode_bhist N))

private theorem kuratowskiEmbeddingToEventFlow_injective {x y : KuratowskiEmbeddingUp} :
    kuratowskiEmbeddingToEventFlow x = kuratowskiEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) =
        kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow y) :=
    congrArg kuratowskiEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kuratowskiEmbedding_round_trip x).symm
      (Eq.trans hread (kuratowskiEmbedding_round_trip y)))

instance kuratowskiEmbeddingBHistCarrier : BHistCarrier KuratowskiEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiEmbeddingToEventFlow
  fromEventFlow := kuratowskiEmbeddingFromEventFlow

instance kuratowskiEmbeddingChapterTasteGate : ChapterTasteGate KuratowskiEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) = some x
    exact kuratowskiEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kuratowskiEmbeddingToEventFlow_injective heq)

theorem KuratowskiEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist, kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist h) = h) ∧
      (∀ x : KuratowskiEmbeddingUp,
        kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) = some x) ∧
        (∀ x y : KuratowskiEmbeddingUp,
          kuratowskiEmbeddingToEventFlow x = kuratowskiEmbeddingToEventFlow y → x = y) ∧
          kuratowskiEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact kuratowskiEmbedding_decode_encode_bhist
  · constructor
    · exact kuratowskiEmbedding_round_trip
    · constructor
      · intro x y heq
        exact kuratowskiEmbeddingToEventFlow_injective heq
      · rfl

end BEDC.Derived.KuratowskiEmbeddingUp
