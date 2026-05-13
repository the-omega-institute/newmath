import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyWindowFusionUp : Type where
  | mk (R W S D E H C P N : BHist) : RegularCauchyWindowFusionUp
  deriving DecidableEq

def regularCauchyWindowFusionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyWindowFusionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyWindowFusionEncodeBHist h

def regularCauchyWindowFusionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyWindowFusionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyWindowFusionDecodeBHist tail)

private theorem regularCauchyWindowFusionDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyWindowFusionDecodeBHist
        (regularCauchyWindowFusionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyWindowFusionToEventFlow :
    RegularCauchyWindowFusionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyWindowFusionUp.mk R W S D E H C P N =>
      [[BMark.b0],
        regularCauchyWindowFusionEncodeBHist R,
        [BMark.b1, BMark.b0],
        regularCauchyWindowFusionEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowFusionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowFusionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowFusionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowFusionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWindowFusionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyWindowFusionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyWindowFusionEncodeBHist N]

def regularCauchyWindowFusionFromEventFlow :
    EventFlow → Option RegularCauchyWindowFusionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RegularCauchyWindowFusionUp.mk
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    R)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    W)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    S)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    D)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    E)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    H)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    C)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    P)
                                                                                  (regularCauchyWindowFusionDecodeBHist
                                                                                    N))
                                                                          | _ :: _ =>
                                                                              none

private theorem regularCauchyWindowFusion_round_trip :
    ∀ x : RegularCauchyWindowFusionUp,
      regularCauchyWindowFusionFromEventFlow
        (regularCauchyWindowFusionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W S D E H C P N =>
      change
        some
          (RegularCauchyWindowFusionUp.mk
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist R))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist W))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist S))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist D))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist E))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist H))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist C))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist P))
            (regularCauchyWindowFusionDecodeBHist
              (regularCauchyWindowFusionEncodeBHist N))) =
          some (RegularCauchyWindowFusionUp.mk R W S D E H C P N)
      rw [regularCauchyWindowFusionDecode_encode_bhist R,
        regularCauchyWindowFusionDecode_encode_bhist W,
        regularCauchyWindowFusionDecode_encode_bhist S,
        regularCauchyWindowFusionDecode_encode_bhist D,
        regularCauchyWindowFusionDecode_encode_bhist E,
        regularCauchyWindowFusionDecode_encode_bhist H,
        regularCauchyWindowFusionDecode_encode_bhist C,
        regularCauchyWindowFusionDecode_encode_bhist P,
        regularCauchyWindowFusionDecode_encode_bhist N]

private theorem regularCauchyWindowFusionToEventFlow_injective
    {x y : RegularCauchyWindowFusionUp} :
    regularCauchyWindowFusionToEventFlow x =
      regularCauchyWindowFusionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyWindowFusionFromEventFlow
          (regularCauchyWindowFusionToEventFlow x) =
        regularCauchyWindowFusionFromEventFlow
          (regularCauchyWindowFusionToEventFlow y) :=
    congrArg regularCauchyWindowFusionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyWindowFusion_round_trip x).symm
      (Eq.trans hread (regularCauchyWindowFusion_round_trip y)))

instance regularCauchyWindowFusionBHistCarrier :
    BHistCarrier RegularCauchyWindowFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyWindowFusionToEventFlow
  fromEventFlow := regularCauchyWindowFusionFromEventFlow

instance regularCauchyWindowFusionChapterTasteGate :
    ChapterTasteGate RegularCauchyWindowFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyWindowFusionFromEventFlow
        (regularCauchyWindowFusionToEventFlow x) = some x
    exact regularCauchyWindowFusion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyWindowFusionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyWindowFusionUp :=
  regularCauchyWindowFusionChapterTasteGate

theorem RegularCauchyWindowFusionUpTasteGate_single_carrier_alignment :
    (∀ x : RegularCauchyWindowFusionUp,
      ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : RegularCauchyWindowFusionUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact ChapterTasteGate.no_hidden_input x
  · intro x w m hw hm
    exact ChapterTasteGate.conservativity x w m hw hm

end BEDC.Derived.RegularCauchyWindowFusionUp
