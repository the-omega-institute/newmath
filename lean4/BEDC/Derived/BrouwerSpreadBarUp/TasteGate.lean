import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerSpreadBarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerSpreadBarUp : Type where
  | mk (S B R L W A H C P N : BHist) : BrouwerSpreadBarUp
  deriving DecidableEq

def brouwerSpreadBarEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerSpreadBarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerSpreadBarEncodeBHist h

def brouwerSpreadBarDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerSpreadBarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerSpreadBarDecodeBHist tail)

private theorem brouwerSpreadBar_decode_encode_bhist :
    ∀ h : BHist, brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerSpreadBarToEventFlow : BrouwerSpreadBarUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerSpreadBarUp.mk S B R L W A H C P N =>
      [[BMark.b0],
        brouwerSpreadBarEncodeBHist S,
        [BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        brouwerSpreadBarEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        brouwerSpreadBarEncodeBHist N]

def brouwerSpreadBarFromEventFlow : EventFlow → Option BrouwerSpreadBarUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | W :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | A :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (BrouwerSpreadBarUp.mk
                                                                                          (brouwerSpreadBarDecodeBHist S)
                                                                                          (brouwerSpreadBarDecodeBHist B)
                                                                                          (brouwerSpreadBarDecodeBHist R)
                                                                                          (brouwerSpreadBarDecodeBHist L)
                                                                                          (brouwerSpreadBarDecodeBHist W)
                                                                                          (brouwerSpreadBarDecodeBHist A)
                                                                                          (brouwerSpreadBarDecodeBHist H)
                                                                                          (brouwerSpreadBarDecodeBHist C)
                                                                                          (brouwerSpreadBarDecodeBHist P)
                                                                                          (brouwerSpreadBarDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem brouwerSpreadBar_mk_congr
    {S S' B B' R R' L L' W W' A A' H H' C C' P P' N N' : BHist}
    (hS : S' = S)
    (hB : B' = B)
    (hR : R' = R)
    (hL : L' = L)
    (hW : W' = W)
    (hA : A' = A)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    BrouwerSpreadBarUp.mk S' B' R' L' W' A' H' C' P' N' =
      BrouwerSpreadBarUp.mk S B R L W A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hB
  cases hR
  cases hL
  cases hW
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem brouwerSpreadBar_round_trip :
    ∀ x : BrouwerSpreadBarUp,
      brouwerSpreadBarFromEventFlow (brouwerSpreadBarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B R L W A H C P N =>
      change
        some
          (BrouwerSpreadBarUp.mk
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist S))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist B))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist R))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist L))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist W))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist A))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist H))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist C))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist P))
            (brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist N))) =
          some (BrouwerSpreadBarUp.mk S B R L W A H C P N)
      exact
        congrArg some
          (brouwerSpreadBar_mk_congr
            (brouwerSpreadBar_decode_encode_bhist S)
            (brouwerSpreadBar_decode_encode_bhist B)
            (brouwerSpreadBar_decode_encode_bhist R)
            (brouwerSpreadBar_decode_encode_bhist L)
            (brouwerSpreadBar_decode_encode_bhist W)
            (brouwerSpreadBar_decode_encode_bhist A)
            (brouwerSpreadBar_decode_encode_bhist H)
            (brouwerSpreadBar_decode_encode_bhist C)
            (brouwerSpreadBar_decode_encode_bhist P)
            (brouwerSpreadBar_decode_encode_bhist N))

private theorem brouwerSpreadBarToEventFlow_injective {x y : BrouwerSpreadBarUp} :
    brouwerSpreadBarToEventFlow x = brouwerSpreadBarToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerSpreadBarFromEventFlow (brouwerSpreadBarToEventFlow x) =
        brouwerSpreadBarFromEventFlow (brouwerSpreadBarToEventFlow y) :=
    congrArg brouwerSpreadBarFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (brouwerSpreadBar_round_trip x).symm
      (Eq.trans hread (brouwerSpreadBar_round_trip y)))

instance brouwerSpreadBarBHistCarrier : BHistCarrier BrouwerSpreadBarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerSpreadBarToEventFlow
  fromEventFlow := brouwerSpreadBarFromEventFlow

instance brouwerSpreadBarChapterTasteGate : ChapterTasteGate BrouwerSpreadBarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerSpreadBarFromEventFlow (brouwerSpreadBarToEventFlow x) = some x
    exact brouwerSpreadBar_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (brouwerSpreadBarToEventFlow_injective heq)

theorem BrouwerSpreadBarTasteGate_single_carrier_alignment :
    (∀ h : BHist, brouwerSpreadBarDecodeBHist (brouwerSpreadBarEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BrouwerSpreadBarUp) ∧
        Nonempty (ChapterTasteGate BrouwerSpreadBarUp) ∧
          brouwerSpreadBarEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact brouwerSpreadBar_decode_encode_bhist
  · constructor
    · exact ⟨brouwerSpreadBarBHistCarrier⟩
    · constructor
      · exact ⟨brouwerSpreadBarChapterTasteGate⟩
      · rfl

end BEDC.Derived.BrouwerSpreadBarUp
