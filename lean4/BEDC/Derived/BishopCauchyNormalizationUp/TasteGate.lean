import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyNormalizationUp : Type where
  | mk (S M phi W D R E H C P N : BHist) : BishopCauchyNormalizationUp

def bishopCauchyNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyNormalizationEncodeBHist h

def bishopCauchyNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyNormalizationDecodeBHist tail)

private theorem bishopCauchyNormalization_decode_encode_bhist :
    ∀ h : BHist,
      bishopCauchyNormalizationDecodeBHist (bishopCauchyNormalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem bishopCauchyNormalization_mk_congr
    {S S' M M' phi phi' W W' D D' R R' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hM : M' = M) (hphi : phi' = phi) (hW : W' = W)
    (hD : D' = D) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    BishopCauchyNormalizationUp.mk S' M' phi' W' D' R' E' H' C' P' N' =
      BishopCauchyNormalizationUp.mk S M phi W D R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hphi
  cases hW
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def bishopCauchyNormalizationFields : BishopCauchyNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyNormalizationUp.mk S M phi W D R E H C P N =>
      [S, M, phi, W, D, R, E, H, C, P, N]

def bishopCauchyNormalizationToEventFlow : BishopCauchyNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCauchyNormalizationFields x).map bishopCauchyNormalizationEncodeBHist

def bishopCauchyNormalizationFromEventFlow : EventFlow → Option BishopCauchyNormalizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | phi :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (BishopCauchyNormalizationUp.mk
                                                      (bishopCauchyNormalizationDecodeBHist S)
                                                      (bishopCauchyNormalizationDecodeBHist M)
                                                      (bishopCauchyNormalizationDecodeBHist phi)
                                                      (bishopCauchyNormalizationDecodeBHist W)
                                                      (bishopCauchyNormalizationDecodeBHist D)
                                                      (bishopCauchyNormalizationDecodeBHist R)
                                                      (bishopCauchyNormalizationDecodeBHist E)
                                                      (bishopCauchyNormalizationDecodeBHist H)
                                                      (bishopCauchyNormalizationDecodeBHist C)
                                                      (bishopCauchyNormalizationDecodeBHist P)
                                                      (bishopCauchyNormalizationDecodeBHist N))
                                              | _ :: _ => none

private theorem bishopCauchyNormalization_round_trip :
    ∀ x : BishopCauchyNormalizationUp,
      bishopCauchyNormalizationFromEventFlow
        (bishopCauchyNormalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M phi W D R E H C P N =>
      exact
        congrArg some
          (bishopCauchyNormalization_mk_congr
            (bishopCauchyNormalization_decode_encode_bhist S)
            (bishopCauchyNormalization_decode_encode_bhist M)
            (bishopCauchyNormalization_decode_encode_bhist phi)
            (bishopCauchyNormalization_decode_encode_bhist W)
            (bishopCauchyNormalization_decode_encode_bhist D)
            (bishopCauchyNormalization_decode_encode_bhist R)
            (bishopCauchyNormalization_decode_encode_bhist E)
            (bishopCauchyNormalization_decode_encode_bhist H)
            (bishopCauchyNormalization_decode_encode_bhist C)
            (bishopCauchyNormalization_decode_encode_bhist P)
            (bishopCauchyNormalization_decode_encode_bhist N))

private theorem bishopCauchyNormalizationToEventFlow_injective
    {x y : BishopCauchyNormalizationUp} :
    bishopCauchyNormalizationToEventFlow x =
      bishopCauchyNormalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyNormalizationFromEventFlow (bishopCauchyNormalizationToEventFlow x) =
        bishopCauchyNormalizationFromEventFlow (bishopCauchyNormalizationToEventFlow y) :=
    congrArg bishopCauchyNormalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCauchyNormalization_round_trip x).symm
      (Eq.trans hread (bishopCauchyNormalization_round_trip y)))

instance bishopCauchyNormalizationBHistCarrier :
    BHistCarrier BishopCauchyNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyNormalizationToEventFlow
  fromEventFlow := bishopCauchyNormalizationFromEventFlow

instance bishopCauchyNormalizationChapterTasteGate :
    ChapterTasteGate BishopCauchyNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCauchyNormalizationFromEventFlow
      (bishopCauchyNormalizationToEventFlow x) = some x
    exact bishopCauchyNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyNormalizationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCauchyNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyNormalizationChapterTasteGate

theorem BishopCauchyNormalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCauchyNormalizationDecodeBHist
      (bishopCauchyNormalizationEncodeBHist h) = h) ∧
      (∀ x : BishopCauchyNormalizationUp,
        bishopCauchyNormalizationFromEventFlow
          (bishopCauchyNormalizationToEventFlow x) = some x) ∧
        (∀ x y : BishopCauchyNormalizationUp,
          bishopCauchyNormalizationToEventFlow x =
            bishopCauchyNormalizationToEventFlow y → x = y) ∧
          bishopCauchyNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bishopCauchyNormalization_decode_encode_bhist
  · constructor
    · exact bishopCauchyNormalization_round_trip
    · constructor
      · intro x y heq
        exact bishopCauchyNormalizationToEventFlow_injective heq
      · rfl

end BEDC.Derived.BishopCauchyNormalizationUp
