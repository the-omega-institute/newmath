import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteFourierTailProjectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteFourierTailProjectorUp : Type where
  | mk (K A W D S R E H C P N : BHist) : FiniteFourierTailProjectorUp
  deriving DecidableEq

def FiniteFourierTailProjectorUp_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: FiniteFourierTailProjectorUp_encodeBHist h
  | BHist.e1 h => BMark.b1 :: FiniteFourierTailProjectorUp_encodeBHist h

def FiniteFourierTailProjectorUp_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (FiniteFourierTailProjectorUp_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (FiniteFourierTailProjectorUp_decodeBHist tail)

private theorem FiniteFourierTailProjectorUp_decode_encode :
    ∀ h : BHist,
      FiniteFourierTailProjectorUp_decodeBHist
          (FiniteFourierTailProjectorUp_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FiniteFourierTailProjectorUp_fields :
    FiniteFourierTailProjectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteFourierTailProjectorUp.mk K A W D S R E H C P N =>
      [K, A, W, D, S, R, E, H, C, P, N]

def FiniteFourierTailProjectorUp_toEventFlow :
    FiniteFourierTailProjectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (FiniteFourierTailProjectorUp_fields x).map
      FiniteFourierTailProjectorUp_encodeBHist

def FiniteFourierTailProjectorUp_fromEventFlow :
    EventFlow → Option FiniteFourierTailProjectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
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
                                                    (FiniteFourierTailProjectorUp.mk
                                                      (FiniteFourierTailProjectorUp_decodeBHist K)
                                                      (FiniteFourierTailProjectorUp_decodeBHist A)
                                                      (FiniteFourierTailProjectorUp_decodeBHist W)
                                                      (FiniteFourierTailProjectorUp_decodeBHist D)
                                                      (FiniteFourierTailProjectorUp_decodeBHist S)
                                                      (FiniteFourierTailProjectorUp_decodeBHist R)
                                                      (FiniteFourierTailProjectorUp_decodeBHist E)
                                                      (FiniteFourierTailProjectorUp_decodeBHist H)
                                                      (FiniteFourierTailProjectorUp_decodeBHist C)
                                                      (FiniteFourierTailProjectorUp_decodeBHist P)
                                                      (FiniteFourierTailProjectorUp_decodeBHist N))
                                              | _ :: _ => none

private theorem FiniteFourierTailProjectorUp_round_trip :
    ∀ x : FiniteFourierTailProjectorUp,
      FiniteFourierTailProjectorUp_fromEventFlow
          (FiniteFourierTailProjectorUp_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K A W D S R E H C P N =>
      change
        some
          (FiniteFourierTailProjectorUp.mk
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist K))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist A))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist W))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist D))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist S))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist R))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist E))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist H))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist C))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist P))
            (FiniteFourierTailProjectorUp_decodeBHist
              (FiniteFourierTailProjectorUp_encodeBHist N))) =
          some (FiniteFourierTailProjectorUp.mk K A W D S R E H C P N)
      rw [FiniteFourierTailProjectorUp_decode_encode K,
        FiniteFourierTailProjectorUp_decode_encode A,
        FiniteFourierTailProjectorUp_decode_encode W,
        FiniteFourierTailProjectorUp_decode_encode D,
        FiniteFourierTailProjectorUp_decode_encode S,
        FiniteFourierTailProjectorUp_decode_encode R,
        FiniteFourierTailProjectorUp_decode_encode E,
        FiniteFourierTailProjectorUp_decode_encode H,
        FiniteFourierTailProjectorUp_decode_encode C,
        FiniteFourierTailProjectorUp_decode_encode P,
        FiniteFourierTailProjectorUp_decode_encode N]

private theorem FiniteFourierTailProjectorUp_toEventFlow_injective
    {x y : FiniteFourierTailProjectorUp} :
    FiniteFourierTailProjectorUp_toEventFlow x =
        FiniteFourierTailProjectorUp_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FiniteFourierTailProjectorUp_fromEventFlow
          (FiniteFourierTailProjectorUp_toEventFlow x) =
        FiniteFourierTailProjectorUp_fromEventFlow
          (FiniteFourierTailProjectorUp_toEventFlow y) :=
    congrArg FiniteFourierTailProjectorUp_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteFourierTailProjectorUp_round_trip x).symm
      (Eq.trans hread (FiniteFourierTailProjectorUp_round_trip y)))

instance FiniteFourierTailProjectorUp_BHistCarrier :
    BHistCarrier FiniteFourierTailProjectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FiniteFourierTailProjectorUp_toEventFlow
  fromEventFlow := FiniteFourierTailProjectorUp_fromEventFlow

instance FiniteFourierTailProjectorUp_ChapterTasteGate :
    ChapterTasteGate FiniteFourierTailProjectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FiniteFourierTailProjectorUp_fromEventFlow
          (FiniteFourierTailProjectorUp_toEventFlow x) =
        some x
    exact FiniteFourierTailProjectorUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteFourierTailProjectorUp_toEventFlow_injective heq)

instance FiniteFourierTailProjectorUp_Nontrivial :
    Nontrivial FiniteFourierTailProjectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteFourierTailProjectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteFourierTailProjectorUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def FiniteFourierTailProjectorUp_taste_gate :
    ChapterTasteGate FiniteFourierTailProjectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FiniteFourierTailProjectorUp_ChapterTasteGate

theorem FiniteFourierTailProjectorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteFourierTailProjectorUp) ∧
      FiniteFourierTailProjectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty ≠
        FiniteFourierTailProjectorUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨FiniteFourierTailProjectorUp_ChapterTasteGate⟩
  · intro h
    cases h

end BEDC.Derived.FiniteFourierTailProjectorUp
