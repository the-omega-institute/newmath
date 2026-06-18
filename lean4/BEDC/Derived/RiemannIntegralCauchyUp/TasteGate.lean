import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegralCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannIntegralCauchyUp : Type where
  | mk (G D I R E H C P N : BHist) : RiemannIntegralCauchyUp
  deriving DecidableEq

def RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist h

def RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
        (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RiemannIntegralCauchyTasteGate_single_carrier_alignment_fields :
    RiemannIntegralCauchyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegralCauchyUp.mk G D I R E H C P N => [G, D, I, R, E, H, C, P, N]

def RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow :
    RiemannIntegralCauchyUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RiemannIntegralCauchyTasteGate_single_carrier_alignment_fields x).map
      RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist

def RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option RiemannIntegralCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | G :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | I :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
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
                                            (RiemannIntegralCauchyUp.mk
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist G)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist D)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist I)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist R)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist E)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist H)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist C)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist P)
                                              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist N))
                                      | _ :: _ => none

private theorem RiemannIntegralCauchyTasteGate_single_carrier_alignment_round_trip :
    forall x : RiemannIntegralCauchyUp,
      RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow
        (RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G D I R E H C P N =>
      change
        some
          (RiemannIntegralCauchyUp.mk
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist G))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist D))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist I))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist R))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist E))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist H))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist C))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist P))
            (RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
              (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RiemannIntegralCauchyUp.mk G D I R E H C P N)
      rw [RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode G,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode D,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode I,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode R,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode E,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode H,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode C,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode P,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannIntegralCauchyUp} :
    RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow x =
      RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow
          (RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow x) =
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow
          (RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannIntegralCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannIntegralCauchyTasteGate_single_carrier_alignment_round_trip y)))

instance riemannIntegralCauchyBHistCarrier : BHistCarrier RiemannIntegralCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow

instance riemannIntegralCauchyChapterTasteGate :
    ChapterTasteGate RiemannIntegralCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow
        (RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
    exact RiemannIntegralCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RiemannIntegralCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannIntegralCauchyChapterTasteGate

theorem RiemannIntegralCauchyTasteGate_single_carrier_alignment :
    (forall G D I R E H C P N : BHist,
      RiemannIntegralCauchyTasteGate_single_carrier_alignment_fields
        (RiemannIntegralCauchyUp.mk G D I R E H C P N) =
          [G, D, I, R, E, H, C, P, N]) ∧
      (forall h : BHist,
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_decodeBHist
          (RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] ∧
          Nonempty (ChapterTasteGate RiemannIntegralCauchyUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  have gate : ChapterTasteGate RiemannIntegralCauchyUp := {
    round_trip := by
      intro x
      change
        RiemannIntegralCauchyTasteGate_single_carrier_alignment_fromEventFlow
          (RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow x) =
            some x
      exact RiemannIntegralCauchyTasteGate_single_carrier_alignment_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy (RiemannIntegralCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq) }
  constructor
  · intro G D I R E H C P N
    rfl
  · constructor
    · exact RiemannIntegralCauchyTasteGate_single_carrier_alignment_decode_encode
    · constructor
      · rfl
      · exact ⟨gate⟩

end BEDC.Derived.RiemannIntegralCauchyUp
