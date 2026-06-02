import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailBallUp : Type where
  | mk (R S D Q W E H C P N : BHist) : RegularCauchyTailBallUp
  deriving DecidableEq

def regularCauchyTailBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailBallEncodeBHist h

def regularCauchyTailBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailBallDecodeBHist tail)

private theorem regularCauchyTailBallDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailBallFields : RegularCauchyTailBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailBallUp.mk R S D Q W E H C P N => [R, S, D, Q, W, E, H, C, P, N]

def regularCauchyTailBallToEventFlow : RegularCauchyTailBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailBallFields x).map regularCauchyTailBallEncodeBHist

def regularCauchyTailBallFromEventFlow : EventFlow → Option RegularCauchyTailBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (RegularCauchyTailBallUp.mk
                                                  (regularCauchyTailBallDecodeBHist R)
                                                  (regularCauchyTailBallDecodeBHist S)
                                                  (regularCauchyTailBallDecodeBHist D)
                                                  (regularCauchyTailBallDecodeBHist Q)
                                                  (regularCauchyTailBallDecodeBHist W)
                                                  (regularCauchyTailBallDecodeBHist E)
                                                  (regularCauchyTailBallDecodeBHist H)
                                                  (regularCauchyTailBallDecodeBHist C)
                                                  (regularCauchyTailBallDecodeBHist P)
                                                  (regularCauchyTailBallDecodeBHist N))
                                          | _ :: _ => none

private theorem regularCauchyTailBall_round_trip :
    ∀ x : RegularCauchyTailBallUp,
      regularCauchyTailBallFromEventFlow (regularCauchyTailBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D Q W E H C P N =>
      change
        some
          (RegularCauchyTailBallUp.mk
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist R))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist S))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist D))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist Q))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist W))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist E))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist H))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist C))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist P))
            (regularCauchyTailBallDecodeBHist (regularCauchyTailBallEncodeBHist N))) =
          some (RegularCauchyTailBallUp.mk R S D Q W E H C P N)
      rw [regularCauchyTailBallDecode_encode_bhist R,
        regularCauchyTailBallDecode_encode_bhist S,
        regularCauchyTailBallDecode_encode_bhist D,
        regularCauchyTailBallDecode_encode_bhist Q,
        regularCauchyTailBallDecode_encode_bhist W,
        regularCauchyTailBallDecode_encode_bhist E,
        regularCauchyTailBallDecode_encode_bhist H,
        regularCauchyTailBallDecode_encode_bhist C,
        regularCauchyTailBallDecode_encode_bhist P,
        regularCauchyTailBallDecode_encode_bhist N]

private theorem regularCauchyTailBallToEventFlow_injective
    {x y : RegularCauchyTailBallUp} :
    regularCauchyTailBallToEventFlow x = regularCauchyTailBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailBallFromEventFlow (regularCauchyTailBallToEventFlow x) =
        regularCauchyTailBallFromEventFlow (regularCauchyTailBallToEventFlow y) :=
    congrArg regularCauchyTailBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailBall_round_trip x).symm
      (Eq.trans hread (regularCauchyTailBall_round_trip y)))

instance regularCauchyTailBallBHistCarrier : BHistCarrier RegularCauchyTailBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailBallToEventFlow
  fromEventFlow := regularCauchyTailBallFromEventFlow

instance regularCauchyTailBallChapterTasteGate :
    ChapterTasteGate RegularCauchyTailBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTailBallFromEventFlow (regularCauchyTailBallToEventFlow x) = some x
    exact regularCauchyTailBall_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailBallToEventFlow_injective heq)

theorem RegularCauchyTailBallTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyTailBallDecodeBHist
      (regularCauchyTailBallEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyTailBallUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyTailBallUp) ∧
          regularCauchyTailBallEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact regularCauchyTailBallDecode_encode_bhist
  · constructor
    · exact ⟨regularCauchyTailBallBHistCarrier⟩
    · constructor
      · exact ⟨regularCauchyTailBallChapterTasteGate⟩
      · rfl

end BEDC.Derived.RegularCauchyTailBallUp
