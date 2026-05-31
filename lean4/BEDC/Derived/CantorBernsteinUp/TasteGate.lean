import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorBernsteinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorBernsteinUp : Type where
  | mk :
      (source target injectionForward injectionBackward zigzag classifier boundary transport replay
        provenance name : BHist) →
        CantorBernsteinUp

def CantorBernsteinTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b1]

def CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist h

def CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CantorBernsteinTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
          (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow :
    CantorBernsteinUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CantorBernsteinUp.mk source target injectionForward injectionBackward zigzag classifier
      boundary transport replay provenance name =>
      [CantorBernsteinTasteGate_single_carrier_alignment_tag,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist source,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist target,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist injectionForward,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist injectionBackward,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist zigzag,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist classifier,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist boundary,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist transport,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist replay,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist provenance,
        CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist name]

def CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CantorBernsteinUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | target :: rest2 =>
              match rest2 with
              | [] => none
              | injectionForward :: rest3 =>
                  match rest3 with
                  | [] => none
                  | injectionBackward :: rest4 =>
                      match rest4 with
                      | [] => none
                      | zigzag :: rest5 =>
                          match rest5 with
                          | [] => none
                          | classifier :: rest6 =>
                              match rest6 with
                              | [] => none
                              | boundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (CantorBernsteinUp.mk
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            source)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            target)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            injectionForward)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            injectionBackward)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            zigzag)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            classifier)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            boundary)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            transport)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            replay)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            provenance)
                                                          (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
                                                            name))
                                                  | _ :: _ => none

private theorem CantorBernsteinTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CantorBernsteinUp,
      CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow
          (CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target injectionForward injectionBackward zigzag classifier boundary transport replay
      provenance name =>
      change
        some
          (CantorBernsteinUp.mk
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist source))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist target))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist injectionForward))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist injectionBackward))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist zigzag))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist classifier))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist boundary))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist transport))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist replay))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist provenance))
            (CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
              (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist name))) =
          some
            (CantorBernsteinUp.mk source target injectionForward injectionBackward zigzag
              classifier boundary transport replay provenance name)
      rw [CantorBernsteinTasteGate_single_carrier_alignment_decode_encode source,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode target,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode injectionForward,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode injectionBackward,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode zigzag,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode classifier,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode boundary,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode transport,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode replay,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode provenance,
        CantorBernsteinTasteGate_single_carrier_alignment_decode_encode name]

private theorem CantorBernsteinTasteGate_single_carrier_alignment_injective
    {x y : CantorBernsteinUp} :
    CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow x =
        CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow
          (CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow x) =
        CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow
          (CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CantorBernsteinTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CantorBernsteinTasteGate_single_carrier_alignment_round_trip y)))

instance CantorBernsteinTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CantorBernsteinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow

instance CantorBernsteinTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CantorBernsteinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow
          (CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CantorBernsteinTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorBernsteinTasteGate_single_carrier_alignment_injective heq)

theorem CantorBernsteinTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        CantorBernsteinTasteGate_single_carrier_alignment_decodeBHist
            (CantorBernsteinTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      (∀ x : CantorBernsteinUp,
        CantorBernsteinTasteGate_single_carrier_alignment_fromEventFlow
            (CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow x) =
          some x) ∧
        (∀ x y : CantorBernsteinUp,
          CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow x =
              CantorBernsteinTasteGate_single_carrier_alignment_toEventFlow y →
            x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CantorBernsteinTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CantorBernsteinTasteGate_single_carrier_alignment_round_trip
    · intro x y heq
      exact CantorBernsteinTasteGate_single_carrier_alignment_injective heq

end BEDC.Derived.CantorBernsteinUp
