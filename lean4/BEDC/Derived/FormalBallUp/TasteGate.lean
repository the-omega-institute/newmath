import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalBallUp : Type where
  | mk
      (metric radius dyadic window transport replay provenance localName : BHist) :
      FormalBallUp
  deriving DecidableEq

def formalBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalBallEncodeBHist h

def formalBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalBallDecodeBHist tail)

private theorem formalBallDecode_encode_bhist :
    ∀ h : BHist, formalBallDecodeBHist (formalBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def formalBallFields : FormalBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FormalBallUp.mk metric radius dyadic window transport replay provenance localName =>
      [metric, radius, dyadic, window, transport, replay, provenance, localName]

def formalBallToEventFlow : FormalBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FormalBallUp.mk metric radius dyadic window transport replay provenance localName =>
      [formalBallEncodeBHist metric,
        formalBallEncodeBHist radius,
        formalBallEncodeBHist dyadic,
        formalBallEncodeBHist window,
        formalBallEncodeBHist transport,
        formalBallEncodeBHist replay,
        formalBallEncodeBHist provenance,
        formalBallEncodeBHist localName]

def formalBallFromEventFlow : EventFlow → Option FormalBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | metric :: rest0 =>
      match rest0 with
      | radius :: rest1 =>
          match rest1 with
          | dyadic :: rest2 =>
              match rest2 with
              | window :: rest3 =>
                  match rest3 with
                  | transport :: rest4 =>
                      match rest4 with
                      | replay :: rest5 =>
                          match rest5 with
                          | provenance :: rest6 =>
                              match rest6 with
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (FormalBallUp.mk
                                          (formalBallDecodeBHist metric)
                                          (formalBallDecodeBHist radius)
                                          (formalBallDecodeBHist dyadic)
                                          (formalBallDecodeBHist window)
                                          (formalBallDecodeBHist transport)
                                          (formalBallDecodeBHist replay)
                                          (formalBallDecodeBHist provenance)
                                          (formalBallDecodeBHist localName))
                                  | _ :: _ => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none

private theorem formalBall_round_trip :
    ∀ x : FormalBallUp, formalBallFromEventFlow (formalBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric radius dyadic window transport replay provenance localName =>
      change
        some
          (FormalBallUp.mk
            (formalBallDecodeBHist (formalBallEncodeBHist metric))
            (formalBallDecodeBHist (formalBallEncodeBHist radius))
            (formalBallDecodeBHist (formalBallEncodeBHist dyadic))
            (formalBallDecodeBHist (formalBallEncodeBHist window))
            (formalBallDecodeBHist (formalBallEncodeBHist transport))
            (formalBallDecodeBHist (formalBallEncodeBHist replay))
            (formalBallDecodeBHist (formalBallEncodeBHist provenance))
            (formalBallDecodeBHist (formalBallEncodeBHist localName))) =
          some (FormalBallUp.mk metric radius dyadic window transport replay provenance localName)
      rw [formalBallDecode_encode_bhist metric, formalBallDecode_encode_bhist radius,
        formalBallDecode_encode_bhist dyadic, formalBallDecode_encode_bhist window,
        formalBallDecode_encode_bhist transport, formalBallDecode_encode_bhist replay,
        formalBallDecode_encode_bhist provenance, formalBallDecode_encode_bhist localName]

private theorem formalBallToEventFlow_injective {x y : FormalBallUp} :
    formalBallToEventFlow x = formalBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalBallFromEventFlow (formalBallToEventFlow x) =
        formalBallFromEventFlow (formalBallToEventFlow y) :=
    congrArg formalBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (formalBall_round_trip x).symm
      (Eq.trans hread (formalBall_round_trip y)))

instance formalBallBHistCarrier : BHistCarrier FormalBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalBallToEventFlow
  fromEventFlow := formalBallFromEventFlow

instance formalBallChapterTasteGate : ChapterTasteGate FormalBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change formalBallFromEventFlow (formalBallToEventFlow x) = some x
    exact formalBall_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (formalBallToEventFlow_injective heq)

theorem FormalBallTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FormalBallUp) ∧
      Nonempty (ChapterTasteGate FormalBallUp) ∧
        (∀ h : BHist, formalBallDecodeBHist (formalBallEncodeBHist h) = h) ∧
          (∀ x : FormalBallUp, formalBallFromEventFlow (formalBallToEventFlow x) = some x) ∧
            formalBallEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro formalBallBHistCarrier
  · constructor
    · exact Nonempty.intro formalBallChapterTasteGate
    · constructor
      · exact formalBallDecode_encode_bhist
      · constructor
        · exact formalBall_round_trip
        · rfl

end BEDC.Derived.FormalBallUp
